-- Prove2me | solution 1 for BFAlmostLinear.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-22T01:52:55.657412+00:00
-- url     : https://prove2.me/submissions/d4407af8-2577-4919-8cec-56f2cb1ecd1a

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
theorem BFAlmostLinear.lemma_2_4 :
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

namespace BFAlmostLinear

open Classical in
/-- Averaging the weighted incidences finds one vertex in at least a `1/q` fraction of the sets. -/
private theorem exists_many_incident {V R : Type} [Fintype V] (I : Finset R) (w : V → ℝ)
    (A : R → Finset V) (q : ℕ) (hw : ∀ v, 0 ≤ w v) (hW : 0 < ∑ v, w v)
    (hlarge : ∀ r ∈ I, (∑ v, w v) ≤ (q : ℝ) * ∑ v ∈ A r, w v) :
    ∃ v, I.card ≤ q * (I.filter fun r => v ∈ A r).card := by
  let hits (v : V) := (I.filter fun r => v ∈ A r).card
  have hmass : (I.card : ℝ) * (∑ v, w v) ≤ ∑ v, ((q : ℝ) * (hits v : ℝ)) * w v := by
    calc
      _ = ∑ _r ∈ I, ∑ v, w v := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ I, (q : ℝ) * ∑ v ∈ A r, w v := Finset.sum_le_sum hlarge
      _ = ∑ r ∈ I, ∑ v, if v ∈ A r then (q : ℝ) * w v else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum, ← Finset.sum_filter,
          Finset.filter_mem_eq_of_subset (Finset.subset_univ (A r))]
      _ = ∑ v, ∑ r ∈ I, if v ∈ A r then (q : ℝ) * w v else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        unfold hits
        ring
  by_contra! h
  have hstrict (v : V) : (q : ℝ) * (hits v : ℝ) < I.card := by exact_mod_cast h v
  have hzero : (∑ _v : V, (0 : ℝ)) < ∑ v, w v := by simpa using hW
  obtain ⟨v, hv, hvpos⟩ := Finset.exists_lt_of_sum_lt hzero
  have hlt : (∑ u, ((q : ℝ) * (hits u : ℝ)) * w u) < (I.card : ℝ) * (∑ u, w u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum
      (fun u _ => mul_le_mul_of_nonneg_right (hstrict u).le (hw u))
      ⟨v, hv, mul_lt_mul_of_pos_right (hstrict v) hvpos⟩
  exact (not_lt_of_ge hmass) hlt

open Classical in
/-- At most `q` vertices suffice to meet at least half the weighted-large sets. -/
theorem exists_weighted_cover_half {V R : Type} [Fintype V] (I : Finset R) (w : V → ℝ)
    (A : R → Finset V) (q : ℕ) (hq : 0 < q) (hw : ∀ v, 0 ≤ w v)
    (hW : 0 < ∑ v, w v) (hlarge : ∀ r ∈ I, (∑ v, w v) ≤ (q : ℝ) * ∑ v ∈ A r, w v) :
    ∃ S : Finset V, S.card ≤ q ∧ I.card ≤ 2 * (I.filter fun r => ¬ Disjoint S (A r)).card := by
  let covered (S : Finset V) := I.filter fun r => ¬ Disjoint S (A r)
  have grow (k : ℕ) (hk : k ≤ q) :
      ∃ S : Finset V, S.card ≤ k ∧ k * I.card ≤ 2 * q * (covered S).card := by
    induction k with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨S, hsize, hcount⟩ := ih ((Nat.le_succ k).trans hk)
      by_cases hhalf : I.card ≤ 2 * (covered S).card
      · refine ⟨S, hsize.trans (Nat.le_succ k), ?_⟩
        calc
          (k + 1) * I.card ≤ q * I.card := Nat.mul_le_mul_right _ hk
          _ ≤ q * (2 * (covered S).card) := Nat.mul_le_mul_left _ hhalf
          _ = _ := by ac_rfl
      · let remaining := I.filter fun r => Disjoint S (A r)
        have hpartition : remaining.card + (covered S).card = I.card :=
          Finset.card_filter_add_card_filter_not (s := I) (fun r => Disjoint S (A r))
        have hremaining : I.card ≤ 2 * remaining.card := by omega
        have hlargeRemaining : ∀ r ∈ remaining, (∑ v, w v) ≤ (q : ℝ) * ∑ v ∈ A r, w v :=
          fun r hr => hlarge r (Finset.mem_filter.mp hr).1
        obtain ⟨v, hv⟩ := exists_many_incident remaining w A q hw hW hlargeRemaining
        let fresh := remaining.filter fun r => v ∈ A r
        have hfresh : I.card ≤ 2 * q * fresh.card := by
          calc
            _ ≤ 2 * remaining.card := hremaining
            _ ≤ 2 * (q * fresh.card) := Nat.mul_le_mul_left 2 hv
            _ = _ := (Nat.mul_assoc _ _ _).symm
        have hcoverUnion : covered (insert v S) = covered S ∪ fresh := by
          ext r
          simp only [covered, fresh, remaining, Finset.mem_filter, Finset.mem_union,
            Finset.disjoint_insert_left]
          tauto
        have hdisjoint : Disjoint (covered S) fresh := by
          rw [Finset.disjoint_left]
          intro r hr hf
          exact (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
        have hnewCard : (covered (insert v S)).card = (covered S).card + fresh.card := by
          rw [hcoverUnion, Finset.card_union_of_disjoint hdisjoint]
        refine ⟨insert v S, (Finset.card_insert_le v S).trans (Nat.succ_le_succ hsize), ?_⟩
        calc
          (k + 1) * I.card = k * I.card + I.card := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ (2 * q) * (covered S).card + (2 * q) * fresh.card := Nat.add_le_add hcount hfresh
          _ = _ := by rw [hnewCard, Nat.mul_add]
  obtain ⟨S, hsize, hcount⟩ := grow q le_rfl
  refine ⟨S, hsize, Nat.le_of_mul_le_mul_left ?_ hq⟩
  calc
    q * I.card ≤ 2 * q * (covered S).card := hcount
    _ = _ := by ac_rfl

open Classical in
/-- Applying the half cover on each side produces one rectangle meeting at least a quarter of
the indices on both sides. -/
theorem exists_weighted_cover_rectangle {V R : Type} [Fintype V] (I : Finset R)
    (wIn wOut : V → ℝ) (AIn AOut : R → Finset V) (qIn qOut : ℕ)
    (hqIn : 0 < qIn) (hqOut : 0 < qOut)
    (hwIn : ∀ v, 0 ≤ wIn v) (hwOut : ∀ v, 0 ≤ wOut v)
    (hWIn : 0 < ∑ v, wIn v) (hWOut : 0 < ∑ v, wOut v)
    (hlargeIn : ∀ r ∈ I, (∑ v, wIn v) ≤ (qIn : ℝ) * ∑ v ∈ AIn r, wIn v)
    (hlargeOut : ∀ r ∈ I, (∑ v, wOut v) ≤ (qOut : ℝ) * ∑ v ∈ AOut r, wOut v) :
    ∃ S T : Finset V, S.card ≤ qIn ∧ T.card ≤ qOut ∧
      I.card ≤ 4 * (I.filter fun r => ¬ Disjoint S (AIn r) ∧ ¬ Disjoint T (AOut r)).card := by
  obtain ⟨S, hS, hhalfIn⟩ := exists_weighted_cover_half I wIn AIn qIn hqIn hwIn hWIn hlargeIn
  let hitIn := I.filter fun r => ¬ Disjoint S (AIn r)
  change I.card ≤ 2 * hitIn.card at hhalfIn
  have hlargeOut' : ∀ r ∈ hitIn, (∑ v, wOut v) ≤ (qOut : ℝ) * ∑ v ∈ AOut r, wOut v :=
    fun r hr => hlargeOut r (Finset.mem_filter.mp hr).1
  obtain ⟨T, hT, hhalfOut⟩ :=
    exists_weighted_cover_half hitIn wOut AOut qOut hqOut hwOut hWOut hlargeOut'
  refine ⟨S, T, hS, hT, ?_⟩
  rw [show (I.filter fun r => ¬ Disjoint S (AIn r) ∧ ¬ Disjoint T (AOut r)) =
    hitIn.filter (fun r => ¬ Disjoint T (AOut r)) from (Finset.filter_filter _ _ _).symm]
  omega

end BFAlmostLinear

namespace BFAlmostLinear

open Classical in
/-- If rectangles of width q hit at most Bq centers, then for every endpoint weight
distribution there are at most 4Bq centers with both search sets of mass at least W/q. -/
theorem weighted_rectangle_tail {V R : Type} [Fintype V] (N : Finset R)
    (X : V → R → V → Prop) (B : ℝ) (hB : 0 ≤ B)
    (rectangle : ∀ S T : Finset V, S.card = T.card →
      ((N.filter fun r => ∃ s ∈ S, ∃ t ∈ T, X s r t).card : ℝ) ≤ B * (S.card : ℝ))
    (A Z : R → Finset V) (hbox : ∀ r ∈ N, ∀ s ∈ A r, ∀ t ∈ Z r, X s r t)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hW : 0 < ∑ v, w v) (q : ℕ) (hq : 0 < q) :
    ((N.filter fun r => (∑ v, w v) ≤ (q : ℝ) *
      min (∑ v ∈ A r, w v) (∑ v ∈ Z r, w v)).card : ℝ) ≤ (4 * B) * (q : ℝ) := by
  let I := N.filter fun r => (∑ v, w v) ≤ (q : ℝ) *
      min (∑ v ∈ A r, w v) (∑ v ∈ Z r, w v)
  have hin (r : R) (hr : r ∈ I) := (Finset.mem_filter.mp hr).2
  have hq' : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  obtain ⟨S,T,hS,hT,hhits⟩ := exists_weighted_cover_rectangle I w w A Z q q hq hq
    hw hw hW hW (fun r hr => (hin r hr).trans <| mul_le_mul_of_nonneg_left (min_le_left _ _) hq')
      (fun r hr => (hin r hr).trans <| mul_le_mul_of_nonneg_left (min_le_right _ _) hq')
  let k := max S.card T.card
  have hkn : k ≤ (Finset.univ : Finset V).card := max_le (Finset.card_le_univ S) (Finset.card_le_univ T)
  obtain ⟨S', hSS, _, hs'⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) (le_max_left _ _) hkn
  obtain ⟨T', hTT, _, ht'⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ T) (le_max_right _ _) hkn
  have incl : (I.filter fun r => ¬ Disjoint S (A r) ∧ ¬ Disjoint T (Z r)) ⊆
      (N.filter fun r => ∃ s ∈ S', ∃ t ∈ T', X s r t) := by
    intro r hr
    obtain ⟨hrI, ha, hz⟩ := Finset.mem_filter.mp hr
    have hrN : r ∈ N := (Finset.mem_filter.mp hrI).1
    obtain ⟨s, hs, hsa⟩ := Finset.not_disjoint_iff.mp ha
    obtain ⟨t, ht, htz⟩ := Finset.not_disjoint_iff.mp hz
    exact Finset.mem_filter.mpr ⟨hrN,s,hSS hs,t,hTT ht,hbox r hrN s hsa t htz⟩
  have hc := hhits.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card incl))
  have hr := rectangle S' T' (hs'.trans ht'.symm)
  have hkq : S'.card ≤ q := hs'.trans_le (max_le hS hT)
  change (I.card : ℝ) ≤ _
  calc
    _ ≤ 4 * ((N.filter fun r => ∃ s ∈ S', ∃ t ∈ T', X s r t).card : ℝ) := by exact_mod_cast hc
    _ ≤ 4 * (B * (S'.card : ℝ)) := by gcongr
    _ ≤ (4 * B) * (q : ℝ) := by rw [← mul_assoc]; gcongr

end BFAlmostLinear

namespace BFAlmostLinear

open Classical in
/-- A bound on the number of centers above each reciprocal scale gives a bound on their total mass. -/
theorem sum_mass_le_of_dyadic_tail {α : Type*} (I : Finset α) (f : α → ℝ)
    (W L : ℝ) (hW : 0 < W) (hf : ∀ r ∈ I, 0 ≤ f r ∧ f r ≤ W)
    (htail : ∀ q : ℕ, 0 < q →
      ((I.filter fun r => W ≤ (q : ℝ) * f r).card : ℝ) ≤ L * (q : ℝ))
    (J : ℕ) (hJ : I.card ≤ 2 ^ J) :
    (∑ r ∈ I, f r) ≤ W * (1 + 2 * (J : ℝ) * L) := by
  let threshold (j : ℕ) := W / (2 : ℝ) ^ j
  let trimmed (j : ℕ) := ∑ r ∈ I, min (f r) (threshold j)
  have hthreshold (j : ℕ) : 0 ≤ threshold j := by
    unfold threshold
    positivity
  have hstep (j : ℕ) : trimmed j ≤ trimmed (j + 1) + 2 * W * L := by
    let q := (2 : ℕ) ^ (j + 1)
    have hq : 0 < q := by unfold q; positivity
    have hcut (r : α) : threshold (j + 1) ≤ f r ↔ W ≤ (q : ℝ) * f r := by
      unfold threshold q
      rw [div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (j + 1)), mul_comm (f r)]
      push_cast
      rfl
    calc
      trimmed j ≤ ∑ r ∈ I,
          (min (f r) (threshold (j + 1)) + if W ≤ (q : ℝ) * f r then threshold j else 0) := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases h : W ≤ (q : ℝ) * f r
        · rw [if_pos h]
          exact (min_le_right _ _).trans
            (le_add_of_nonneg_left (le_min (hf r hr).1 (hthreshold (j + 1))))
        · rw [if_neg h, add_zero, min_eq_left (le_of_lt (lt_of_not_ge (hcut r |>.not.mpr h)))]
          exact min_le_left _ _
      _ = trimmed (j + 1) +
          ((I.filter fun r => W ≤ (q : ℝ) * f r).card : ℝ) * threshold j := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [← Finset.sum_filter]
        simp
      _ ≤ trimmed (j + 1) + (L * (q : ℝ)) * threshold j :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (htail q hq) (hthreshold j))
      _ = trimmed (j + 1) + 2 * W * L := by
        unfold q threshold
        push_cast
        rw [pow_succ]
        field_simp
  have hsteps (j : ℕ) : trimmed 0 ≤ trimmed j + (j : ℝ) * (2 * W * L) := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        trimmed 0 ≤ trimmed j + (j : ℝ) * (2 * W * L) := ih
        _ ≤ trimmed (j + 1) + 2 * W * L + (j : ℝ) * (2 * W * L) :=
          add_le_add (hstep j) le_rfl
        _ = trimmed j.succ + (j.succ : ℝ) * (2 * W * L) := by
          push_cast
          ring
  have hbudget : trimmed J ≤ W := by
    have hJ' : (I.card : ℝ) ≤ (2 : ℝ) ^ J := by exact_mod_cast hJ
    calc
      trimmed J ≤ ∑ _r ∈ I, threshold J := Finset.sum_le_sum fun _ _ => min_le_right _ _
      _ = (I.card : ℝ) * threshold J := by simp
      _ ≤ (2 : ℝ) ^ J * threshold J := mul_le_mul_of_nonneg_right hJ' (hthreshold J)
      _ = W := by unfold threshold; field_simp
  have hinitial : trimmed 0 = ∑ r ∈ I, f r := by
    unfold trimmed threshold
    exact Finset.sum_congr rfl fun r hr => by simp [min_eq_left (hf r hr).2]
  calc
    (∑ r ∈ I, f r) = trimmed 0 := hinitial.symm
    _ ≤ trimmed J + (J : ℝ) * (2 * W * L) := hsteps J
    _ ≤ W + (J : ℝ) * (2 * W * L) := add_le_add hbudget le_rfl
    _ = W * (1 + 2 * (J : ℝ) * L) := by ring

/-- A sufficient number of dyadic layers grows at most logarithmically in the number of vertices. -/
theorem dyadicDepth_log_bound (n : ℕ) (hn : 2 ≤ n) :
    n ≤ 2 ^ (Nat.log 2 n + 1) ∧
      ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (2 / Real.log 2) * Real.log (n : ℝ) := by
  refine ⟨(Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le, ?_⟩
  have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpow
  have htwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) htwo
  have hscaled : ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
    push_cast
    linarith only [hlog, hlogn]
  calc
    _ ≤ (2 * Real.log (n : ℝ)) / Real.log 2 := (le_div_iff₀ hlog₂).2 hscaled
    _ = (2 / Real.log 2) * Real.log (n : ℝ) := by ring


end BFAlmostLinear

namespace BFAlmostLinear

open Classical in
/-- A sample works simultaneously for all nonnegative vertex tolls. -/
def uniformWeightedGood {V E : Type} [Fintype V] (G : WGraph V E) (N : Finset V)
    (b K : ℝ) (h₁ h₂ : ℕ) (U : Finset V) : Prop :=
  ∀ lam : V → ℝ, (∀ v, 0 ≤ lam v) →
    ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ → ∀ Vin Vout : V → Finset V,
      (∀ r ∈ N, ∀ s ∈ Vin r, ∀ t ∈ Vout r, G.InX h₁ h₂ ϕ s r t) →
      ∑ r ∈ N, min (∑ v ∈ Vin r, lam v) (∑ v ∈ Vout r, lam v) ≤
        K * (∑ v, lam v) * b * Real.log (Fintype.card V) ^ 2

open Classical in
theorem goodMass_mono_event {V : Type} (N : Finset V) (b : ℝ) (hb : 1 ≤ b)
    (P Q : Finset V → Prop) (implies : ∀ U, P U → Q U) :
    goodMass N b P ≤ goodMass N b Q := by
  unfold goodMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro U hU
    obtain ⟨inSupport, satisfies⟩ := Finset.mem_filter.mp hU
    exact Finset.mem_filter.mpr ⟨inSupport, implies U satisfies⟩
  · exact fun U _ _ => sampleMass_nonneg N U hb

private noncomputable def weightedConstant (K : ℝ) : ℝ :=
  1 / (Real.log 2) ^ 2 + 16 * K / Real.log 2

open Classical in
private theorem weighted_levels_bound {V R : Type} [Fintype V] (N : Finset R)
    (hN : N.card ≤ Fintype.card V) (hn : 2 ≤ Fintype.card V)
    (K b : ℝ) (hK : 0 < K) (hb : 1 ≤ b)
    (lam : V → ℝ) (hlam : ∀ v, 0 ≤ lam v) (f : R → ℝ)
    (hf : ∀ r ∈ N, 0 ≤ f r ∧ f r ≤ ∑ v, lam v)
    (tail : 0 < ∑ v, lam v → ∀ q : ℕ, 0 < q →
      ((N.filter fun r => (∑ v, lam v) ≤ (q : ℝ) * f r).card : ℝ) ≤
        (4 * (K * b * Real.log (Fintype.card V))) * (q : ℝ)) :
    ∑ r ∈ N, f r ≤ weightedConstant K * (∑ v, lam v) * b * Real.log (Fintype.card V) ^ 2 := by
  let n := Fintype.card V
  let W := ∑ v, lam v
  have hW : 0 ≤ W := Finset.sum_nonneg fun v _ => hlam v
  by_cases hWzero : W = 0
  · have hsum : ∑ r ∈ N, f r ≤ 0 := by
      calc
        _ ≤ ∑ _r ∈ N, W := Finset.sum_le_sum fun r hr => (hf r hr).2
        _ = 0 := by simp [hWzero]
    simpa only [show (∑ v, lam v) = 0 from hWzero, mul_zero, zero_mul] using hsum
  · have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm hWzero)
    let J := Nat.log 2 n + 1
    let L := Real.log (n : ℝ)
    let d := Real.log 2
    have hd : 0 < d := Real.log_pos (by norm_num)
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hdL : d ≤ L := Real.log_le_log (by norm_num) hnreal
    have hL : 0 ≤ L := hd.le.trans hdL
    have hbpos : 0 ≤ b := zero_le_one.trans hb
    have hB : 0 ≤ 4 * (K * b * L) := by positivity
    obtain ⟨hnpow, hJ⟩ := dyadicDepth_log_bound n hn
    have hlevels := sum_mass_le_of_dyadic_tail N f W (4 * (K * b * L)) hWpos hf
      (tail hWpos) J (hN.trans hnpow)
    have hmain : 2 * (J : ℝ) * (4 * (K * b * L)) ≤ (16 * K / d) * b * L ^ 2 := by
      calc
        _ ≤ 2 * ((2 / d) * L) * (4 * (K * b * L)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (by norm_num)) hB
        _ = _ := by ring
    have hbase : (1 : ℝ) ≤ (1 / d ^ 2) * b * L ^ 2 := by
      have hsq : d ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hd.le hdL 2
      have hmul : L ^ 2 ≤ b * L ^ 2 := le_mul_of_one_le_left (sq_nonneg L) hb
      calc
        1 ≤ (b * L ^ 2) / d ^ 2 := (le_div_iff₀ (pow_pos hd 2)).2 (by simpa using hsq.trans hmul)
        _ = _ := by ring
    calc
      _ ≤ W * (1 + 2 * (J : ℝ) * (4 * (K * b * L))) := hlevels
      _ ≤ W * ((1 / d ^ 2) * b * L ^ 2 + (16 * K / d) * b * L ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hbase hmain) hW
      _ = weightedConstant K * W * b * L ^ 2 := by unfold weightedConstant d; ring

open Classical in
theorem uniform_corollary_2_8 :
    ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V)
        (b : ℝ) (h₁ h₂ : ℕ), G.Frozen → 1 ≤ b →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤ goodMass N b (uniformWeightedGood G N b K h₁ h₂) := by
  intro c hc
  obtain ⟨K, hK, rectangle_probability⟩ := lemma_2_4 c hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨weightedConstant K, by unfold weightedConstant; positivity, ?_⟩
  intro V E _ _ G N b h₁ h₂ frozen hb
  let n := Fintype.card V
  have hN : N.card ≤ n := Finset.card_le_univ N
  by_cases hn : 2 ≤ n
  · refine (rectangle_probability V E G N b h₁ h₂ frozen hb).trans ?_
    apply goodMass_mono_event N b hb
    intro U good lam hlam ϕ hfix Vin Vout hbox
    let X := G.InX h₁ h₂ ϕ
    let B := K * b * Real.log (n : ℝ)
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have logNonneg : 0 ≤ Real.log (n : ℝ) := (Real.log_pos hnreal).le
    have hB : 0 ≤ B := by unfold B; positivity
    have rectangle : ∀ S T : Finset V, S.card = T.card →
        ((N.filter fun r => ∃ s ∈ S, ∃ t ∈ T, X s r t).card : ℝ) ≤ B * (S.card : ℝ) := by
      intro S T hst
      by_cases hS : S.Nonempty
      · have positive : 1 ≤ S.card := Finset.card_pos.mpr hS
        calc
          _ ≤ K * b * (S.card : ℝ) * Real.log (n : ℝ) :=
            good S.card positive (Finset.card_le_univ S) S T rfl hst.symm ϕ hfix
          _ = _ := by unfold B; ring
      · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
    apply weighted_levels_bound N hN hn K b hK hb lam hlam
    · intro r hr
      refine ⟨le_min (Finset.sum_nonneg fun v _ => hlam v) (Finset.sum_nonneg fun v _ => hlam v), ?_⟩
      exact (min_le_left _ _).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hlam v))
    · intro hW q hq
      exact weighted_rectangle_tail N X B hB rectangle Vin Vout hbox lam hlam hW q hq
  · have small : n = 0 ∨ n = 1 := by omega
    rcases small with zero | one
    · have empty : N = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hN.trans_eq zero))
      have allGood : ∀ U, uniformWeightedGood G N b (weightedConstant K) h₁ h₂ U := by
        intro U lam hlam ϕ hfix Vin Vout hbox
        simp [empty, show Fintype.card V = 0 from zero]
      have full : goodMass N b (uniformWeightedGood G N b (weightedConstant K) h₁ h₂) = 1 := by
        unfold goodMass
        rw [Finset.filter_true_of_mem (fun U _ => allGood U), sum_sampleMass_eq_one]
      rw [full]
      exact sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · simpa only [show Fintype.card V = 1 from one, Nat.cast_one, Real.one_rpow, sub_self] using
        goodMass_nonneg N hb (uniformWeightedGood G N b (weightedConstant K) h₁ h₂)

end BFAlmostLinear

open BFAlmostLinear Classical in
theorem BFAlmostLinear.corollary_2_8 :
    ∃ a : ℕ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V) (b : ℝ) (h₁ h₂ : ℕ)
        (lam : V → ℝ),
        G.Frozen → 1 ≤ b → (∀ v, 0 ≤ lam v) →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤
          goodMass N b fun U =>
            ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ → ∀ Vin Vout : V → Finset V,
              (∀ r ∈ N, ∀ s ∈ Vin r, ∀ t ∈ Vout r, G.InX h₁ h₂ ϕ s r t) →
              ∑ r ∈ N, min (∑ v ∈ Vin r, lam v) (∑ v ∈ Vout r, lam v) ≤
                K * (∑ v, lam v) * b * Real.log (Fintype.card V) ^ a := by
  refine ⟨2, ?_⟩
  intro c hc
  obtain ⟨K, hK, uniform⟩ := uniform_corollary_2_8 c hc
  refine ⟨K, hK, ?_⟩
  intro V E _ _ G N b h₁ h₂ lam frozen hb nonneg
  refine (uniform V E G N b h₁ h₂ frozen hb).trans ?_
  apply goodMass_mono_event N b hb
  intro U good
  exact good lam nonneg

open BFAlmostLinear Classical in
theorem solution :
    ∃ a : ℕ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V) (b : ℝ) (h₁ h₂ : ℕ),
        G.Frozen → 1 ≤ b →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤
          goodMass N b fun U =>
            ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ → ∀ Vin Vout : V → Finset V,
              (∀ r ∈ N, ∀ s ∈ Vin r, ∀ t ∈ Vout r, G.InX h₁ h₂ ϕ s r t) →
              ((∑ r ∈ N, min (Vin r).card (Vout r).card : ℕ) : ℝ) ≤
                K * (Fintype.card V : ℝ) * b * Real.log (Fintype.card V) ^ a := by
  obtain ⟨a, weighted⟩ := corollary_2_8
  refine ⟨a, fun c hc => ?_⟩
  obtain ⟨K, hK, specialize⟩ := weighted c hc
  refine ⟨K, hK, ?_⟩
  intro V E _ _ G N b h₁ h₂ frozen hb
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_sum, Nat.cast_min, Finset.card_univ] using
    specialize V E G N b h₁ h₂ (fun _ => 1) frozen hb (fun _ => zero_le_one)
