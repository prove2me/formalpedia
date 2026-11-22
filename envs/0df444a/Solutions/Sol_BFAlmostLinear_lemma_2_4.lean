-- Prove2me | solution 1 for BFAlmostLinear.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-22T01:47:40.576658+00:00
-- url     : https://prove2.me/submissions/fb9f6f87-710c-4c69-9f22-7796ebc2a1e7

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph
import Definitions.Def_BFAlmostLinear_sampleMass

namespace BFAlmostLinear.WGraph

/-- Adding a finite real translates the entire extended real line, including the two infinities. -/
private noncomputable def shiftOrder (c : ℝ) : EReal ≃o EReal where
  toFun x := x + (c : EReal)
  invFun x := x + ((-c : ℝ) : EReal)
  left_inv x := by
    change (x + (c : EReal)) + ((-c : ℝ) : EReal) = x
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  right_inv x := by
    change (x + ((-c : ℝ) : EReal)) + (c : EReal) = x
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right

theorem pathWeight_reweight {V E : Type} (G : WGraph V E) (ϕ : V → ℝ)
    {P : List E} {s t : V} (hp : G.net.IsPathFrom s t P) :
    pathWeight (G.reweight ϕ).w P = pathWeight G.w P + (ϕ s - ϕ t) := by
  induction P generalizing s with
  | nil => change s = t at hp; simp [hp, pathWeight]
  | cons e P ih =>
    obtain ⟨rfl, hp⟩ := hp
    change (G.w e + ϕ (G.net.tail e) - ϕ (G.net.head e)) + pathWeight (G.reweight ϕ).w P =
      (G.w e + pathWeight G.w P) + _
    rw [ih hp]
    ring

theorem dH_reweight {V E : Type} (G : WGraph V E) (ϕ : V → ℝ) (h : ℕ) (s t : V) :
    (G.reweight ϕ).dH h s t = G.dH h s t + ((ϕ s - ϕ t : ℝ) : EReal) := by
  let f := shiftOrder (ϕ s - ϕ t)
  change (⨅ (P : List E) (_ : G.IsRealWalk s t P ∧ G.hops P ≤ h),
    ((pathWeight (G.reweight ϕ).w P : ℝ) : EReal)) =
    f (⨅ (P : List E) (_ : G.IsRealWalk s t P ∧ G.hops P ≤ h), ((pathWeight G.w P : ℝ) : EReal))
  rw [f.map_iInf]
  congr 1
  funext P
  rw [f.map_iInf]
  apply iInf_congr
  intro hp
  exact (congrArg (fun x : ℝ => (x : EReal)) (pathWeight_reweight G ϕ hp.1.1)).trans (EReal.coe_add _ _)

/-- Each bounded-hop walk has at most h terms that can be negative, even if it repeats arcs. -/
theorem dH_ne_bot_of_frozen {V E : Type} [Fintype E] (G : WGraph V E) (hf : G.Frozen)
    (h : ℕ) (s t : V) : G.dH h s t ≠ ⊥ := by
  classical
  let M := ∑ e, |G.w e|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hedge (e : E) : -M ≤ G.w e := by
    have hle : |G.w e| ≤ M := Finset.single_le_sum (fun j _ => abs_nonneg (G.w j)) (Finset.mem_univ e)
    linarith [neg_abs_le (G.w e)]
  have walk_bound (P : List E) : -(G.hops P : ℝ) * M ≤ pathWeight G.w P := by
    induction P with
    | nil => simp [hops, pathWeight]
    | cons e P ih =>
      change _ ≤ G.w e + pathWeight G.w P
      cases he : G.neg e with
      | false =>
        have hw : 0 ≤ G.w e := le_of_not_gt (fun hneg => by simpa [he] using hf e hneg)
        simpa [hops, List.countP_cons, he] using (ih.trans (le_add_of_nonneg_left hw))
      | true =>
        simp only [hops, List.countP_cons, he, if_true, Nat.cast_add,
          Nat.cast_one] at *
        linarith [hedge e]
  have lower : (((-(h : ℝ) * M : ℝ)) : EReal) ≤ G.dH h s t := by
    apply le_iInf
    intro P
    apply le_iInf
    intro hp
    apply EReal.coe_le_coe_iff.mpr
    calc
      _ ≤ -(G.hops P : ℝ) * M := mul_le_mul_of_nonneg_right (neg_le_neg (by exact_mod_cast hp.2)) hM
      _ ≤ _ := walk_bound P
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) lower

theorem inX_affine_iff {V E : Type} (G : WGraph V E) (h₁ h₂ : ℕ)
    (ϕ : V → ℝ) (s r t : V) :
    G.InX h₁ h₂ ϕ s r t ↔
      G.dH h₁ s r + G.dH h₂ r t + ((ϕ s - ϕ t : ℝ) : EReal) < 0 := by
  unfold InX
  rw [dH_reweight, dH_reweight]
  have h : (ϕ s - ϕ t) = (ϕ s - ϕ r) + (ϕ r - ϕ t) := by ring
  rw [h, EReal.coe_add, add_add_add_comm]

end BFAlmostLinear.WGraph

namespace BFAlmostLinear

/-- The masses of all samples in the canonical powerset sum to one. -/
theorem sum_sampleMass_eq_one {V : Type} [DecidableEq V] (N : Finset V) (b : ℝ) :
    ∑ U ∈ N.powerset, sampleMass N U b = 1 := by
  calc
    _ = ∑ U ∈ N.powerset, (1 / b) ^ U.card * (1 - 1 / b) ^ (N.card - U.card) := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [sampleMass, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU)]
    _ = ∑ k ∈ Finset.range (N.card + 1),
        (1 / b) ^ k * (1 - 1 / b) ^ (N.card - k) * (N.card.choose k : ℝ) := by
      rw [Finset.sum_powerset]
      apply Finset.sum_congr rfl
      intro k _
      simpa only [nsmul_eq_mul, mul_comm] using
        Finset.sum_powersetCard k N (fun j => (1 / b) ^ j * (1 - 1 / b) ^ (N.card - j))
    _ = (1 / b + (1 - 1 / b)) ^ N.card := (add_pow _ _ _).symm
    _ = 1 := by rw [show 1 / b + (1 - 1 / b) = 1 by ring, one_pow]

private theorem sample_omit_nonneg {b : ℝ} (hb : 1 ≤ b) : 0 ≤ 1 - 1 / b := by
  have hpos : 0 < b := zero_lt_one.trans_le hb
  exact sub_nonneg.mpr ((div_le_iff₀ hpos).2 (by simpa using hb))

theorem sampleMass_nonneg {V : Type} [DecidableEq V] (N U : Finset V) {b : ℝ}
    (hb : 1 ≤ b) : 0 ≤ sampleMass N U b := by
  have hpos : 0 < b := zero_lt_one.trans_le hb
  exact mul_nonneg (pow_nonneg (one_div_nonneg.mpr hpos.le) _) (pow_nonneg (sample_omit_nonneg hb) _)

open Classical in
theorem goodMass_nonneg {V : Type} (N : Finset V) {b : ℝ} (hb : 1 ≤ b)
    (Good : Finset V → Prop) : 0 ≤ goodMass N b Good :=
  Finset.sum_nonneg fun U _ => sampleMass_nonneg N U hb

open Classical in
theorem goodMass_compl {V : Type} (N : Finset V) (b : ℝ) (Good : Finset V → Prop) :
    goodMass N b (fun U => ¬ Good U) = 1 - goodMass N b Good := by
  have hsplit : goodMass N b Good + goodMass N b (fun U => ¬ Good U) =
      ∑ U ∈ N.powerset, sampleMass N U b := by
    simp only [goodMass, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro U _
    by_cases h : Good U <;> simp [h]
  rw [sum_sampleMass_eq_one] at hsplit
  linarith

open Classical in
/-- The event that the sample misses `A` has exactly one independent omission factor per vertex
of `A`. -/
theorem goodMass_disjoint_eq {V : Type} (N A : Finset V) (b : ℝ) (hA : A ⊆ N) :
    goodMass N b (fun U => Disjoint U A) = (1 - 1 / b) ^ A.card := by
  unfold goodMass
  calc
    _ = ∑ U ∈ (N \ A).powerset, sampleMass (N \ A) U b * (1 - 1 / b) ^ A.card := by
      apply Finset.sum_congr
      · ext U
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff]
      · intro U hmem
        have hU : U ⊆ N \ A := Finset.mem_powerset.mp hmem
        have hUn : U ⊆ N := hU.trans Finset.sdiff_subset
        have hcard : (N \ U).card = ((N \ A) \ U).card + A.card := by
          have hle := Finset.card_le_card hU
          rw [Finset.card_sdiff_of_subset hA] at hle
          have hAle := Finset.card_le_card hA
          rw [Finset.card_sdiff_of_subset hUn, Finset.card_sdiff_of_subset hU,
            Finset.card_sdiff_of_subset hA]
          omega
        rw [sampleMass, hcard, pow_add, sampleMass, mul_assoc]
    _ = _ := by rw [← Finset.sum_mul, sum_sampleMass_eq_one, one_mul]

open Classical in
theorem goodMass_disjoint_le_exp {V : Type} (N A : Finset V) (b : ℝ) (hb : 1 ≤ b)
    (hA : A ⊆ N) : goodMass N b (fun U => Disjoint U A) ≤ Real.exp (-(A.card : ℝ) / b) := by
  have hscalar : 1 - 1 / b ≤ Real.exp (-(1 / b)) := by
    linarith [Real.add_one_le_exp (-(1 / b))]
  rw [goodMass_disjoint_eq N A b hA]
  calc
    _ ≤ Real.exp (-(1 / b)) ^ A.card := pow_le_pow_left₀ (sample_omit_nonneg hb) hscalar _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

open Classical in
/-- A finite family of events covering `Good` bounds its mass by the sum of their masses. -/
theorem goodMass_le_sum_cover {V ι : Type} (N : Finset V) (b : ℝ) (hb : 1 ≤ b)
    (Good : Finset V → Prop) (I : Finset ι) (Event : ι → Finset V → Prop)
    (hcover : ∀ U ⊆ N, Good U → ∃ i ∈ I, Event i U) :
    goodMass N b Good ≤ ∑ i ∈ I, goodMass N b (Event i) := by
  simp only [goodMass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro U hU
  have hnonneg : ∀ i : ι, 0 ≤ if Event i U then sampleMass N U b else 0 := by
    intro i
    split
    · exact sampleMass_nonneg N U hb
    · exact le_rfl
  by_cases hgood : Good U
  · obtain ⟨i, hi, hevent⟩ := hcover U (Finset.mem_powerset.mp hU) hgood
    rw [if_pos hgood]
    have h := Finset.single_le_sum (f := fun i => if Event i U then sampleMass N U b else 0)
      (fun i _ => hnonneg i) hi
    simpa only [if_pos hevent] using h
  · rw [if_neg hgood]
    exact Finset.sum_nonneg fun i _ => hnonneg i

open Classical in
/-- If every failure misses one of the candidate subsets, its mass is bounded by the sum of
the exponential omission bounds. -/
theorem one_sub_goodMass_le_sum_exp_avoidance {V ι : Type} (N : Finset V) (b : ℝ) (hb : 1 ≤ b)
    (Good : Finset V → Prop) (I : Finset ι) (A : ι → Finset V)
    (hA : ∀ i ∈ I, A i ⊆ N) (hbad : ∀ U ⊆ N, ¬ Good U → ∃ i ∈ I, Disjoint U (A i)) :
    1 - goodMass N b Good ≤ ∑ i ∈ I, Real.exp (-((A i).card : ℝ) / b) := by
  rw [← goodMass_compl N b Good]
  exact (goodMass_le_sum_cover N b hb (fun U => ¬ Good U) I (fun i U => Disjoint U (A i)) hbad).trans
    (Finset.sum_le_sum fun i hi => goodMass_disjoint_le_exp N (A i) b hb (hA i hi))

end BFAlmostLinear

namespace BFAlmostLinear

/-- Failure bound for one rectangle size with the absolute constant of Subclaim 2.5. -/
noncomputable def lemma24BudgetConstantTerm (n ℓ : ℕ) (C₀ K : ℝ) : ℝ :=
  ((n ^ (2 * ℓ) : ℕ) : ℝ) * (C₀ * (((n ^ 3) ^ (2 * ℓ) : ℕ) : ℝ)) *
    Real.exp (-(K * (ℓ : ℝ) * Real.log (n : ℝ)))

/-- The additional exponent pays for the absolute pattern-count constant at every level. -/
theorem lemma24BudgetConstant_absorb (n ℓ k : ℕ) (hn : 2 ≤ n) (hℓ : 1 ≤ ℓ)
    (C₀ : ℝ) (hC₀ : C₀ ≤ (2 : ℝ) ^ k) :
    C₀ * Real.exp (-((k : ℝ) * (ℓ : ℝ) * Real.log (n : ℝ))) ≤ 1 := by
  have hn₂ : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn₀ : (0 : ℝ) < (n : ℝ) := by linarith
  have hpower : C₀ ≤ (n : ℝ) ^ (k * ℓ) := by
    calc
      C₀ ≤ (2 : ℝ) ^ k := hC₀
      _ ≤ (n : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hn₂ k
      _ ≤ (n : ℝ) ^ (k * ℓ) := by
        apply pow_le_pow_right₀ hn₁
        simpa using Nat.mul_le_mul_left k hℓ
  have hexp : Real.exp (-((k : ℝ) * (ℓ : ℝ) * Real.log (n : ℝ))) =
      (n : ℝ) ^ (-((k * ℓ : ℕ) : ℝ)) := by
    rw [Real.rpow_def_of_pos hn₀]
    push_cast
    congr 1
    ring
  calc
    _ ≤ (n : ℝ) ^ (k * ℓ) * Real.exp (-((k : ℝ) * (ℓ : ℝ) * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _)
    _ = 1 := by
      rw [hexp, ← Real.rpow_natCast, ← Real.rpow_add hn₀, add_neg_cancel, Real.rpow_zero]

/-- Each admissible rectangle size costs at most one `n`th of the total budget. -/
theorem lemma24BudgetConstantTerm_le (n ℓ k : ℕ) (hn : 2 ≤ n) (hℓ : 1 ≤ ℓ)
    (c C₀ : ℝ) (hc : 0 < c) (hC₀ : C₀ ≤ (2 : ℝ) ^ k) :
    lemma24BudgetConstantTerm n ℓ C₀ (c + 10 + (k : ℝ)) ≤ (n : ℝ) ^ (-c - 1) := by
  have hn₀ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn₁ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hℓ₁ : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hcount : (n : ℝ) ^ (2 * ℓ) * ((n : ℝ) ^ (3 : ℕ)) ^ (2 * ℓ) =
      (n : ℝ) ^ (8 * ℓ) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hexp : Real.exp (-((c + 10) * (ℓ : ℝ) * Real.log (n : ℝ))) =
      (n : ℝ) ^ (-(c + 10) * (ℓ : ℝ)) := by
    rw [Real.rpow_def_of_pos hn₀]
    congr 1
    ring
  have hsplit : Real.exp (-((c + 10 + (k : ℝ)) * (ℓ : ℝ) * Real.log (n : ℝ))) =
      Real.exp (-((c + 10) * (ℓ : ℝ) * Real.log (n : ℝ))) *
        Real.exp (-((k : ℝ) * (ℓ : ℝ) * Real.log (n : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdrop : c + 2 ≤ (c + 2) * (ℓ : ℝ) :=
    le_mul_of_one_le_right (by linarith) hℓ₁
  calc
    _ = ((n : ℝ) ^ (8 * ℓ) * Real.exp (-((c + 10) * (ℓ : ℝ) * Real.log (n : ℝ)))) *
        (C₀ * Real.exp (-((k : ℝ) * (ℓ : ℝ) * Real.log (n : ℝ)))) := by
      unfold lemma24BudgetConstantTerm
      rw [hsplit]
      push_cast
      rw [← hcount]
      ring
    _ ≤ (n : ℝ) ^ (8 * ℓ) * Real.exp (-((c + 10) * (ℓ : ℝ) * Real.log (n : ℝ))) :=
      mul_le_of_le_one_right (by positivity) (lemma24BudgetConstant_absorb n ℓ k hn hℓ C₀ hC₀)
    _ = (n : ℝ) ^ (((8 * ℓ : ℕ) : ℝ) + -(c + 10) * (ℓ : ℝ)) := by
      rw [hexp, ← Real.rpow_natCast, ← Real.rpow_add hn₀]
    _ ≤ (n : ℝ) ^ (-c - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hn₁
      push_cast
      linarith only [hdrop]

/-- The same choice of `K` bounds the sum for each graph size `n ≥ 2`. -/
theorem lemma24BudgetConstantSum_le (n k : ℕ) (hn : 2 ≤ n) (c C₀ : ℝ)
    (hc : 0 < c) (hC₀ : C₀ ≤ (2 : ℝ) ^ k) :
    (∑ ℓ ∈ Finset.Icc 1 n, lemma24BudgetConstantTerm n ℓ C₀ (c + 10 + (k : ℝ))) ≤
      (n : ℝ) ^ (-c) := by
  have hn₀ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ∑ _ℓ ∈ Finset.Icc 1 n, (n : ℝ) ^ (-c - 1) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact lemma24BudgetConstantTerm_le n ℓ k hn (Finset.mem_Icc.mp hℓ).1 c C₀ hc hC₀
    _ = (n : ℝ) * (n : ℝ) ^ (-c - 1) := by simp [Nat.card_Icc]
    _ = (n : ℝ) ^ (-c) := by
      rw [mul_comm (n : ℝ), ← Real.rpow_add_one hn₀.ne', sub_add_cancel]

theorem exists_lemma24BudgetConstant (c C₀ : ℝ) (hc : 0 < c) (_hC₀ : 0 < C₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 2 ≤ n →
      (∑ ℓ ∈ Finset.Icc 1 n, lemma24BudgetConstantTerm n ℓ C₀ K) ≤ (n : ℝ) ^ (-c) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C₀ (by norm_num : (1 : ℝ) < 2)
  exact ⟨c + 10 + (k : ℝ), by positivity,
    fun n hn => lemma24BudgetConstantSum_le n k hn c C₀ hc hk.le⟩


end BFAlmostLinear

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
theorem BFAlmostLinear.lemma24_subclaim25 :
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

namespace BFAlmostLinear

open Classical in
/-- Realizable sign patterns restricted to a rectangle of endpoint pairs. -/
noncomputable def rectangleSignPatterns {V : Type} (N S T : Finset V)
    (negative : (V → ℝ) → V → V → V → Prop) : Finset (Finset (V × V × V)) :=
  (S ×ˢ N ×ˢ T).powerset.filter fun X =>
    ∃ ϕ : V → ℝ, ∀ x ∈ S ×ˢ N ×ˢ T, x ∈ X ↔ negative ϕ x.1 x.2.1 x.2.2

open Classical in
/-- The sample simultaneously controls all rectangle sizes and all fixing potentials. -/
def rectangleGood {V : Type} [Fintype V] (N : Finset V) (b K : ℝ)
    (negative : (V → ℝ) → V → V → V → Prop)
    (fixes : Finset V → (V → ℝ) → Prop) (U : Finset V) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ Fintype.card V → ∀ S T : Finset V, S.card = ℓ → T.card = ℓ →
    ∀ ϕ : V → ℝ, fixes U ϕ →
      ((N.filter fun r => ∃ s ∈ S, ∃ t ∈ T, negative ϕ s r t).card : ℝ) ≤
        K * b * ℓ * Real.log (Fintype.card V)

open Classical in
private noncomputable def rectangleCenterProjection {V : Type} (X : Finset (V × V × V)) : Finset V :=
  X.image (fun x => x.2.1)

open Classical in
private theorem rectangleCenterProjection_sub {V : Type} (N S T : Finset V)
    (negative : (V → ℝ) → V → V → V → Prop)
    {X : Finset (V × V × V)} (hX : X ∈ rectangleSignPatterns N S T negative) :
    rectangleCenterProjection X ⊆ N := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hX).1
  exact (Finset.mem_product.mp (Finset.mem_product.mp (hsub hx)).2).1

open Classical in
private theorem signSlice_witness {V : Type} (N S T : Finset V)
    (negative : (V → ℝ) → V → V → V → Prop) (ϕ : V → ℝ) :
    ∃ X ∈ rectangleSignPatterns N S T negative,
      rectangleCenterProjection X = N.filter (fun r => ∃ s ∈ S, ∃ t ∈ T, negative ϕ s r t) := by
  let X := (S ×ˢ N ×ˢ T).filter fun x => negative ϕ x.1 x.2.1 x.2.2
  refine ⟨X, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ϕ, ?_⟩
    intro x hx
    simp [X, hx]
  · ext r
    constructor
    · intro hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hdom, hneg⟩ := Finset.mem_filter.mp hx
      obtain ⟨hs, hrt⟩ := Finset.mem_product.mp hdom
      obtain ⟨hn, ht⟩ := Finset.mem_product.mp hrt
      exact Finset.mem_filter.mpr ⟨hn, x.1, hs, x.2.2, ht, hneg⟩
    · intro hr
      obtain ⟨hn, s, hs, t, ht, hneg⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_image.mpr ⟨(s, r, t), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs, Finset.mem_product.mpr ⟨hn, ht⟩⟩, hneg⟩, rfl⟩

open Classical in
/-- Count and cover all heavy pattern projections for each admissible rectangle size. -/
theorem one_sub_rectangleGoodMass_le_budget {V : Type} [Fintype V] (N : Finset V)
    (b K C₀ : ℝ) (hb : 1 ≤ b) (hC₀ : 0 < C₀)
    (negative : (V → ℝ) → V → V → V → Prop)
    (fixes : Finset V → (V → ℝ) → Prop)
    (fixes_excludes : ∀ U ϕ, fixes U ϕ → ∀ r ∈ U, ∀ s t, ¬ negative ϕ s r t)
    (pattern_bound : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ Fintype.card V →
      ∀ S T : Finset V, S.card = ℓ → T.card = ℓ →
        ((rectangleSignPatterns N S T negative).card : ℝ) ≤
          C₀ * (((Fintype.card V ^ 3) ^ (2 * ℓ) : ℕ) : ℝ))
    (union_bound : ∀ {ι : Type} (Good : Finset V → Prop) (I : Finset ι) (A : ι → Finset V),
      (∀ i ∈ I, A i ⊆ N) → (∀ U ⊆ N, ¬ Good U → ∃ i ∈ I, Disjoint U (A i)) →
      1 - goodMass N b Good ≤ ∑ i ∈ I, Real.exp (-((A i).card : ℝ) / b)) :
    1 - goodMass N b (rectangleGood N b K negative fixes) ≤
      ∑ ℓ ∈ Finset.Icc 1 (Fintype.card V),
        ((Fintype.card V ^ (2 * ℓ) : ℕ) : ℝ) *
          (C₀ * (((Fintype.card V ^ 3) ^ (2 * ℓ) : ℕ) : ℝ)) *
          Real.exp (-(K * (ℓ : ℝ) * Real.log (Fintype.card V))) := by
  let n := Fintype.card V
  let good := rectangleGood N b K negative fixes
  let subsets (ℓ : ℕ) := (Finset.univ : Finset V).powersetCard ℓ
  let rectangles (ℓ : ℕ) := subsets ℓ ×ˢ subsets ℓ
  let heavy (ℓ : ℕ) (st : Finset V × Finset V) :=
    ((rectangleSignPatterns N st.1 st.2 negative).image rectangleCenterProjection).filter
      fun A => K * b * (ℓ : ℝ) * Real.log (n : ℝ) < (A.card : ℝ)
  let candidates (ℓ : ℕ) := (rectangles ℓ).sigma (heavy ℓ)
  let I := (Finset.Icc 1 n).sigma candidates
  let A (i : Σ _ : ℕ, Σ _ : Finset V × Finset V, Finset V) := i.2.2
  have domain : ∀ i ∈ I, A i ⊆ N := by
    intro i hi
    have hheavy := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hi).2).2
    obtain ⟨X, hX, hproj⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hheavy).1
    change i.2.2 ⊆ N
    rw [← hproj]
    exact rectangleCenterProjection_sub _ _ _ _ hX
  have cover : ∀ U ⊆ N, ¬ good U → ∃ i ∈ I, Disjoint U (A i) := by
    intro U _ hbad
    simp only [good, rectangleGood, not_forall, not_le] at hbad
    obtain ⟨ℓ, hℓ₁, hℓn, S, T, hS, hT, ϕ, hfix, hbig⟩ := hbad
    obtain ⟨X, hX, hproj⟩ := signSlice_witness N S T negative ϕ
    let idx : Σ _ : ℕ, Σ _ : Finset V × Finset V, Finset V :=
      ⟨ℓ, (S, T), rectangleCenterProjection X⟩
    refine ⟨idx, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hℓ₁, hℓn⟩, ?_⟩, ?_⟩
    · refine Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hX, ?_⟩
        change K * b * (ℓ : ℝ) * Real.log (n : ℝ) < (rectangleCenterProjection X).card
        rwa [hproj]
    · rw [show A idx = rectangleCenterProjection X from rfl, hproj]
      refine Finset.disjoint_left.mpr (fun r hrU hrCenters => ?_)
      obtain ⟨_, s, hs, t, ht, hneg⟩ := Finset.mem_filter.mp hrCenters
      exact fixes_excludes U ϕ hfix r hrU s t hneg
  have rectangle_count (ℓ : ℕ) : (rectangles ℓ).card ≤ n ^ (2 * ℓ) := by
    have hsub : (subsets ℓ).card ≤ n ^ ℓ := by
      simpa only [subsets, Finset.card_powersetCard, Finset.card_univ] using Nat.choose_le_pow n ℓ
    simpa only [rectangles, Finset.card_product, two_mul, pow_add] using Nat.mul_le_mul hsub hsub
  have candidate_count (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 n) :
      ((candidates ℓ).card : ℝ) ≤ ((n ^ (2 * ℓ) : ℕ) : ℝ) *
        (C₀ * (((n ^ 3) ^ (2 * ℓ) : ℕ) : ℝ)) := by
    let limit := C₀ * (((n ^ 3) ^ (2 * ℓ) : ℕ) : ℝ)
    have limit_nonneg : 0 ≤ limit := mul_nonneg hC₀.le (Nat.cast_nonneg _)
    calc
      ((candidates ℓ).card : ℝ) = ∑ st ∈ rectangles ℓ, ((heavy ℓ st).card : ℝ) := by
        simp [candidates, Finset.card_sigma]
      _ ≤ ∑ _st ∈ rectangles ℓ, limit := by
        apply Finset.sum_le_sum
        intro st hst
        obtain ⟨hS, hT⟩ := Finset.mem_product.mp hst
        have hs := (Finset.mem_powersetCard.mp hS).2
        have ht := (Finset.mem_powersetCard.mp hT).2
        have hcard : (heavy ℓ st).card ≤ (rectangleSignPatterns N st.1 st.2 negative).card :=
          (Finset.card_filter_le _ _).trans Finset.card_image_le
        exact (Nat.cast_le.mpr hcard).trans
          (pattern_bound ℓ (Finset.mem_Icc.mp hℓ).1 (Finset.mem_Icc.mp hℓ).2 _ _ hs ht)
      _ = ((rectangles ℓ).card : ℝ) * limit := by simp [nsmul_eq_mul]
      _ ≤ ((n ^ (2 * ℓ) : ℕ) : ℝ) * limit :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (rectangle_count ℓ)) limit_nonneg
  have event_bound (ℓ : ℕ) (i : Σ _ : Finset V × Finset V, Finset V) (hi : i ∈ candidates ℓ) :
      Real.exp (-(i.2.card : ℝ) / b) ≤ Real.exp (-(K * (ℓ : ℝ) * Real.log (n : ℝ))) := by
    have hlarge := (Finset.mem_filter.mp (Finset.mem_sigma.mp hi).2).2
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (zero_lt_one.trans_le hb)).mpr
    calc
      -(i.2.card : ℝ) ≤ -(K * b * (ℓ : ℝ) * Real.log (n : ℝ)) := neg_le_neg hlarge.le
      _ = -(K * (ℓ : ℝ) * Real.log (n : ℝ)) * b := by ring
  calc
    1 - goodMass N b good ≤ ∑ i ∈ I, Real.exp (-((A i).card : ℝ) / b) :=
      union_bound good I A domain cover
    _ = ∑ ℓ ∈ Finset.Icc 1 n, ∑ i ∈ candidates ℓ, Real.exp (-(i.2.card : ℝ) / b) := by
      exact Finset.sum_sigma _ _ _
    _ ≤ ∑ ℓ ∈ Finset.Icc 1 n,
          ((n ^ (2 * ℓ) : ℕ) : ℝ) * (C₀ * (((n ^ 3) ^ (2 * ℓ) : ℕ) : ℝ)) *
            Real.exp (-(K * (ℓ : ℝ) * Real.log (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      calc
        _ ≤ ∑ _i ∈ candidates ℓ, Real.exp (-(K * (ℓ : ℝ) * Real.log (n : ℝ))) :=
          Finset.sum_le_sum (event_bound ℓ)
        _ = ((candidates ℓ).card : ℝ) * Real.exp (-(K * (ℓ : ℝ) * Real.log (n : ℝ))) := by
          simp [nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (candidate_count ℓ hℓ) (Real.exp_pos _).le


end BFAlmostLinear

open BFAlmostLinear Classical in
theorem solution :
    ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V) (b : ℝ) (h₁ h₂ : ℕ),
        G.Frozen → 1 ≤ b →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤
          goodMass N b fun U =>
            ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ Fintype.card V → ∀ S T : Finset V, S.card = ℓ → T.card = ℓ →
              ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ →
                (((N.filter fun r => ∃ s ∈ S, ∃ t ∈ T, G.InX h₁ h₂ ϕ s r t).card : ℕ) : ℝ) ≤
                  K * b * ℓ * Real.log (Fintype.card V) := by
  intro c hc
  obtain ⟨C₀, hC₀, countPatterns⟩ := lemma24_subclaim25
  obtain ⟨K, hK, budget⟩ := exists_lemma24BudgetConstant c C₀ hc hC₀
  refine ⟨K, hK, ?_⟩
  intro V E _ _ G N b h₁ h₂ hf hb
  let n := Fintype.card V
  change 1 - (n : ℝ) ^ (-c) ≤ goodMass N b (rectangleGood N b K (G.InX h₁ h₂) (G.Fixes h₁ h₂))
  by_cases hN : N.Nonempty
  · by_cases hn : 2 ≤ n
    · let weight (s r t : V) := G.dH h₁ s r + G.dH h₂ r t
      have hweight (s r t : V) : weight s r t ≠ ⊥ := by
        exact EReal.add_ne_bot_iff.mpr
          ⟨G.dH_ne_bot_of_frozen hf h₁ s r, G.dH_ne_bot_of_frozen hf h₂ r t⟩
      have pattern_bound (ℓ : ℕ) (hℓ₁ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
          (S T : Finset V) (hS : S.card = ℓ) (hT : T.card = ℓ) :
          ((rectangleSignPatterns N S T (G.InX h₁ h₂)).card : ℝ) ≤
            C₀ * ((((n ^ 3) ^ (2 * ℓ) : ℕ)) : ℝ) := by
        have hSn : S.card ≤ n := hS.trans_le hℓn
        have hTn : T.card ≤ n := hT.trans_le hℓn
        have hNn : N.card ≤ n := Finset.card_le_univ N
        have hSpos : S.Nonempty := Finset.card_pos.mp (hS ▸ hℓ₁)
        have hTpos : T.Nonempty := Finset.card_pos.mp (hT ▸ hℓ₁)
        have hprod : S.card * T.card * N.card ≤ n ^ 3 := by
          simpa only [pow_succ, pow_zero, one_mul] using Nat.mul_le_mul (Nat.mul_le_mul hSn hTn) hNn
        have hdim : (S ∪ T).card ≤ 2 * ℓ := by
          simpa only [hS, hT, two_mul] using Finset.card_union_le S T
        have hbase : 0 < n ^ 3 := pow_pos (by omega) 3
        have hncount : (S.card * T.card * N.card) ^ (S ∪ T).card ≤ (n ^ 3) ^ (2 * ℓ) :=
          (Nat.pow_le_pow_left hprod _).trans (Nat.pow_le_pow_right hbase hdim)
        have hcut := countPatterns V S T N weight hSpos hTpos hN hweight
        have hcut' : ((rectangleSignPatterns N S T (G.InX h₁ h₂)).card : ℝ) ≤
            C₀ * (((S.card * T.card * N.card : ℕ) : ℝ)) ^ (S ∪ T).card := by
          simpa only [rectangleSignPatterns, G.inX_affine_iff, weight] using hcut
        calc
          _ ≤ C₀ * (((S.card * T.card * N.card : ℕ) : ℝ)) ^ (S ∪ T).card := hcut'
          _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hncount) hC₀.le
      have excludes : ∀ U ϕ, G.Fixes h₁ h₂ U ϕ →
          ∀ r ∈ U, ∀ s t, ¬ G.InX h₁ h₂ ϕ s r t := by
        intro U ϕ hfix r hr s t hneg
        exact (not_lt_of_ge (hfix r hr s t)) hneg
      have failure := one_sub_rectangleGoodMass_le_budget N b K C₀ hb hC₀
        (G.InX h₁ h₂) (G.Fixes h₁ h₂) excludes pattern_bound
        (one_sub_goodMass_le_sum_exp_avoidance N b hb)
      have hfailure : 1 - goodMass N b (rectangleGood N b K (G.InX h₁ h₂) (G.Fixes h₁ h₂)) ≤
          (n : ℝ) ^ (-c) := by
        exact failure.trans (budget n hn)
      linarith only [hfailure]
    · have hnpos : 0 < n := (Finset.card_pos.mpr hN).trans_le (Finset.card_le_univ N)
      have hone : n = 1 := by omega
      simpa only [hone, Nat.cast_one, Real.one_rpow, sub_self] using
        goodMass_nonneg N hb (rectangleGood N b K (G.InX h₁ h₂) (G.Fixes h₁ h₂))
  · have emptyN : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    have all_good : ∀ U, rectangleGood N b K (G.InX h₁ h₂) (G.Fixes h₁ h₂) U := by
      intro U ℓ hℓ₁ hℓn S T _ _ ϕ _
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hℓ₁.trans hℓn)
      simp only [emptyN, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      positivity
    have whole_mass : goodMass N b (rectangleGood N b K (G.InX h₁ h₂) (G.Fixes h₁ h₂)) = 1 := by
      unfold goodMass
      rw [Finset.filter_true_of_mem (fun U _ => all_good U), sum_sampleMass_eq_one]
    rw [whole_mass]
    linarith only [Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) (-c)]
