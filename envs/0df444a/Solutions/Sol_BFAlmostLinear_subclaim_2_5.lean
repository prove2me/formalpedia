-- Prove2me | solution 1 for BFAlmostLinear.subclaim_2_5
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-22T01:40:10.484633+00:00
-- url     : https://prove2.me/submissions/dc477d6b-4e1f-4ab9-9437-47196d50dfa4

import Mathlib

namespace BFAlmostLinear

private theorem geom_sum_le_two_mul_pow (q d : ℕ) (hq : 2 ≤ q) :
    ∑ k ∈ Finset.range (d + 1), q ^ k ≤ 2 * q ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have hstep : 2 * q ^ d ≤ q ^ (d + 1) := by
      rw [pow_succ, Nat.mul_comm 2]
      exact Nat.mul_le_mul_left (q ^ d) hq
    calc
      _ ≤ 2 * q ^ d + q ^ (d + 1) := Nat.add_le_add_right ih _
      _ ≤ 2 * q ^ (d + 1) := by omega

open Classical in
/-- A family on a nonempty universe whose shattered sets have size at most `d` has at most
`2 * U.card ^ d` members. -/
theorem count_of_shattered_card_le {ι : Type} (U : Finset ι) (F : Finset (Finset ι)) (d : ℕ)
    (hU : U.Nonempty) (hF : F ⊆ U.powerset) (hsh : ∀ J, F.Shatters J → J.card ≤ d) :
    F.card ≤ 2 * U.card ^ d := by
  by_cases hone : U.card = 1
  · have hcard := Finset.card_le_card hF
    simpa only [Finset.card_powerset, hone, pow_one, one_pow, mul_one] using hcard
  have hcard : 2 ≤ U.card := by
    have hpos := Finset.card_pos.mpr hU
    omega
  let family := (Finset.range (d + 1)).biUnion fun k => U.powersetCard k
  have hsubset : F.shatterer ⊆ family := by
    intro J hJ
    have hJsh := Finset.mem_shatterer.mp hJ
    obtain ⟨W, hW, hJW⟩ := hJsh.exists_superset
    have hJU := hJW.trans (Finset.mem_powerset.mp (hF hW))
    exact Finset.mem_biUnion.mpr ⟨J.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (hsh J hJsh)),
      Finset.mem_powersetCard.mpr ⟨hJU, rfl⟩⟩
  calc
    F.card ≤ F.shatterer.card := Finset.card_le_card_shatterer F
    _ ≤ family.card := Finset.card_le_card hsubset
    _ ≤ ∑ k ∈ Finset.range (d + 1), (U.powersetCard k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (d + 1), U.card ^ k := by
      apply Finset.sum_le_sum
      intro k _
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_pow _ _
    _ ≤ 2 * U.card ^ d := geom_sum_le_two_mul_pow U.card d hcard

end BFAlmostLinear

namespace BFAlmostLinear

/-- If every binary labeling is realized by translating affine inequalities, their normal
vectors are independent. Subtract two realizing parameter values to cancel all offsets. -/
theorem affine_normals_independent {I D : Type} [Fintype I] [Fintype D]
    (a : I → D → ℝ) (b : I → ℝ)
    (realize : ∀ p : I → Prop, ∃ z : D → ℝ,
      ∀ i, p i ↔ b i + ∑ j, a i j * z j < 0) : LinearIndependent ℝ a := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hi
  obtain ⟨zp, hp⟩ := realize (fun i => 0 < c i)
  obtain ⟨zn, hn⟩ := realize (fun i => c i < 0)
  let dot (z : D → ℝ) (k : I) := ∑ j, a k j * z j
  have annihilates (z : D → ℝ) : ∑ k, c k * dot z k = 0 := by
    simp only [dot, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_mul]
    have hj := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
    rw [hj, zero_mul]
  have hpos (k : I) (hk : c k ≠ 0) : 0 < c k * (dot zn k - dot zp k) := by
    rcases lt_or_gt_of_ne hk with h | h
    · apply mul_pos_of_neg_of_neg h
      have h1 := (hn k).mp h
      have h2 := le_of_not_gt (fun hh => (not_lt_of_ge h.le) ((hp k).mpr hh))
      dsimp [dot]
      linarith
    · apply mul_pos h
      have h1 := (hp k).mp h
      have h2 := le_of_not_gt (fun hh => (not_lt_of_ge h.le) ((hn k).mpr hh))
      dsimp [dot]
      linarith
  have sumPos : 0 < ∑ k, c k * (dot zn k - dot zp k) := by
    apply Finset.sum_pos'
    · intro k _
      by_cases hk : c k = 0
      · simp [hk]
      · exact (hpos k hk).le
    · exact ⟨i, Finset.mem_univ i, hpos i hi⟩
  simp only [mul_sub, Finset.sum_sub_distrib, annihilates, sub_self, lt_self_iff_false] at sumPos

open Classical in
theorem affine_shattered_card {ι D : Type} [Fintype D] (U : Finset ι)
    (a : ι → D → ℝ) (b : ι → ℝ) (enabled : ι → Prop) (J : Finset ι)
    (h : (U.powerset.filter fun X => ∃ z : D → ℝ, ∀ i ∈ U,
      i ∈ X ↔ enabled i ∧ b i + ∑ j, a i j * z j < 0).Shatters J) :
    J.card ≤ Fintype.card D := by
  classical
  obtain ⟨big, hbig, hsub⟩ := h.exists_superset
  obtain ⟨hbigU, zb, hb⟩ := Finset.mem_filter.mp hbig
  have hJU := hsub.trans (Finset.mem_powerset.mp hbigU)
  have on (i : J) : enabled i.val := ((hb i (hJU i.property)).mp (hsub i.property)).1
  have ind := affine_normals_independent (fun i : J => a i.val) (fun i : J => b i.val) (by
    intro p
    let marked := fun k => ∃ hk : k ∈ J, p ⟨k,hk⟩
    obtain ⟨X, hX, htrace⟩ := h (Finset.filter_subset marked J)
    obtain ⟨_, z, hz⟩ := Finset.mem_filter.mp hX
    refine ⟨z, fun i => ?_⟩
    have hmem := Finset.ext_iff.mp htrace i.val
    simp only [Finset.mem_inter, Finset.mem_filter, i.property, true_and] at hmem
    have hm : marked i.val ↔ p i := ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨i.property, hp⟩⟩
    rw [← hm, ← hmem, hz i (hJU i.property)]
    simp [on i])
  simpa only [Fintype.card_coe, Module.finrank_pi] using ind.fintype_card_le_finrank

end BFAlmostLinear

namespace BFAlmostLinear

open Classical in
theorem affine_pattern_bound {ι D : Type} (U : Finset ι) [Fintype D] (hU : U.Nonempty)
    (a : ι → D → ℝ) (b : ι → ℝ) (enabled : ι → Prop) :
    (U.powerset.filter fun X => ∃ z : D → ℝ, ∀ i ∈ U,
      i ∈ X ↔ enabled i ∧ b i + ∑ j, a i j * z j < 0).card ≤ 2 * U.card ^ Fintype.card D := by
  apply count_of_shattered_card_le U _ (Fintype.card D) hU (Finset.filter_subset _ _)
  exact affine_shattered_card U a b enabled

end BFAlmostLinear

open Classical in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (S T N : Finset V) (c : V → V → V → EReal),
        S.Nonempty → T.Nonempty → N.Nonempty → (∀ s r t, c s r t ≠ ⊥) →
        ((((S ×ˢ N ×ˢ T).powerset.filter fun X =>
            ∃ ϕ : V → ℝ, ∀ x ∈ S ×ˢ N ×ˢ T,
              x ∈ X ↔ c x.1 x.2.1 x.2.2 + ((ϕ x.1 - ϕ x.2.2 : ℝ) : EReal) < 0).card : ℕ) : ℝ) ≤
          C * (((S.card * T.card * N.card : ℕ) : ℝ)) ^ (S ∪ T).card := by
  refine ⟨2, by norm_num, ?_⟩
  intro V _ S T N c hS hT hN hBot
  let U := S ×ˢ N ×ˢ T
  let D := {v : V // v ∈ S ∪ T}
  let a (x : V × V × V) (j : D) : ℝ :=
    (if j.val = x.1 then 1 else 0) - (if j.val = x.2.2 then 1 else 0)
  let b (x : V × V × V) := (c x.1 x.2.1 x.2.2).toReal
  let enabled (x : V × V × V) : Prop := c x.1 x.2.1 x.2.2 ≠ ⊤
  have sum_selector (z : D → ℝ) (v : D) :
      (∑ j : D, (if j.val = v.val then 1 else 0) * z j) = z v := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro j _ hj
      have hval : j.val ≠ v.val := fun h => hj (Subtype.ext h)
      simp [hval]
    · simp
  have sum_eval (x : V × V × V) (s t : D) (hs : s.val = x.1) (ht : t.val = x.2.2)
      (z : D → ℝ) : (∑ j : D, a x j * z j) = z s - z t := by
    simp_rw [a, ← hs, ← ht, sub_mul]
    rw [Finset.sum_sub_distrib, sum_selector, sum_selector]
  have ereal_eval (x : V × V × V) (p : ℝ) :
      c x.1 x.2.1 x.2.2 + (p : EReal) < 0 ↔ enabled x ∧ b x + p < 0 := by
    by_cases htop : c x.1 x.2.1 x.2.2 = ⊤
    · simp [enabled, htop, EReal.top_add_of_ne_bot]
    · have hon : enabled x := htop
      simp only [hon, true_and]
      change _ ↔ (c x.1 x.2.1 x.2.2).toReal + p < 0
      rw [← EReal.coe_toReal htop (hBot x.1 x.2.1 x.2.2), ← EReal.coe_add]
      exact EReal.coe_lt_coe_iff
  have family_eq : (U.powerset.filter fun X => ∃ ϕ : V → ℝ, ∀ x ∈ U,
      x ∈ X ↔ c x.1 x.2.1 x.2.2 + ((ϕ x.1 - ϕ x.2.2 : ℝ) : EReal) < 0) =
      (U.powerset.filter fun X => ∃ z : D → ℝ, ∀ x ∈ U,
        x ∈ X ↔ enabled x ∧ b x + ∑ j, a x j * z j < 0) := by
    ext X
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨ϕ, hϕ⟩
      let z : D → ℝ := fun v => ϕ v.val
      refine ⟨z, fun x hx => ?_⟩
      have hs : x.1 ∈ S ∪ T := Finset.mem_union_left _ (Finset.mem_product.mp hx).1
      have ht : x.2.2 ∈ S ∪ T := Finset.mem_union_right _
        (Finset.mem_product.mp (Finset.mem_product.mp hx).2).2
      rw [sum_eval x ⟨x.1, hs⟩ ⟨x.2.2, ht⟩ rfl rfl]
      exact (hϕ x hx).trans (ereal_eval x _)
    · rintro ⟨z, hz⟩
      let ϕ (v : V) := if h : v ∈ S ∪ T then z ⟨v, h⟩ else 0
      refine ⟨ϕ, fun x hx => ?_⟩
      have hs : x.1 ∈ S ∪ T := Finset.mem_union_left _ (Finset.mem_product.mp hx).1
      have ht : x.2.2 ∈ S ∪ T := Finset.mem_union_right _
        (Finset.mem_product.mp (Finset.mem_product.mp hx).2).2
      rw [ereal_eval, show ϕ x.1 = z ⟨x.1, hs⟩ by dsimp only [ϕ]; rw [dif_pos hs],
        show ϕ x.2.2 = z ⟨x.2.2, ht⟩ by dsimp only [ϕ]; rw [dif_pos ht],
        ← sum_eval x ⟨x.1, hs⟩ ⟨x.2.2, ht⟩ rfl rfl]
      exact hz x hx
  have hU : U.Nonempty := hS.product (hN.product hT)
  have family_card := BFAlmostLinear.affine_pattern_bound U hU a b enabled
  rw [← family_eq] at family_card
  have dcard : Fintype.card D = (S ∪ T).card := Fintype.card_coe (S ∪ T)
  rw [dcard] at family_card
  simp only [U, Finset.card_product] at family_card
  rw [show S.card * (N.card * T.card) = S.card * T.card * N.card by ac_rfl] at family_card
  exact_mod_cast family_card
