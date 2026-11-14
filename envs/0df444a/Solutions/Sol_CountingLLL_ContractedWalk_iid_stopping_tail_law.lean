-- Prove2me | solution 1 for CountingLLL.ContractedWalk.iid_stopping_tail_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:57:22.783182+00:00
-- url     : https://prove2.me/submissions/465fbf04-38fa-4ff1-a1fc-748a6f22fdef

import Definitions.Def_CountingLLL_ContractedWalk

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

private theorem shift_law (p : ℝ≥0∞) (hp : p ≤ 1) (n : ℕ) :
    (tapeLaw p).map (fun ω k => ω (k+n)) = tapeLaw p := by
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  exact Measure.map_infinitePi_infinitePi_of_inj (f := fun k : ℕ => k+n) (by intro a b h; exact Nat.add_right_cancel h)

private theorem prefix_tail_independent (p : ℝ≥0∞) (hp : p ≤ 1) (n : ℕ) :
    IndepFun (fun ω : Tape => fun j : Fin n => ω j.val)
      (fun ω : Tape => fun k => ω (k+n)) (tapeLaw p) := by
  classical
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  have hind : iIndepFun (fun k (ω : Tape) => ω k) μ := iIndepFun_infinitePi (fun _ => measurable_id)
  have hm : Measurable (fun ω : Tape => fun j : Fin n => ω j.val) := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  apply IndepFun.indepFun_process hm (fun k => measurable_pi_apply (k+n))
  intro I
  let S : Finset ℕ := Finset.range n
  let T : Finset ℕ := I.image (fun k => k+n)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hx' : x < n := Finset.mem_range.mp hx
    obtain ⟨k,hk,hEq⟩ := Finset.mem_image.mp hxt
    omega
  have h := iIndepFun.indepFun_finset S T hd hind (fun k => measurable_pi_apply k)
  let F : (S → Bool) → (Fin n → Bool) := fun x j => x ⟨j.val, Finset.mem_range.mpr j.isLt⟩
  let G : (T → Bool) → (I → Bool) := fun x k => x ⟨k.val+n, Finset.mem_image.mpr ⟨k.val,k.property,rfl⟩⟩
  have hmF : Measurable F := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hmG : Measurable G := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hc := h.comp hmF hmG
  simpa [F,G,S,T,Function.comp_def] using hc

theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) (τ : Tape → ℕ)
    (hτ : ∀ n ω ω', (∀ k < n, ω k = ω' k) → (τ ω = n ↔ τ ω' = n)) :
    (tapeLaw p).map (fun ω k => ω (k+τ ω)) = tapeLaw p := by
  classical
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  let E : ℕ → Set Tape := fun n => {ω | τ ω = n}
  let pref : (n : ℕ) → Tape → (Fin n → Bool) := fun n ω j => ω j.val
  let F : (n : ℕ) → Set (Fin n → Bool) := fun n => {x | ∃ ω : Tape, pref n ω = x ∧ τ ω = n}
  have hpref (n : ℕ) : Measurable (pref n) := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  have hpre (n : ℕ) : pref n ⁻¹' F n = E n := by
    ext ω
    constructor
    · rintro ⟨ω', heq, hn⟩
      have he : ∀ k < n, ω k = ω' k := by intro k hk; exact (congrFun heq ⟨k,hk⟩).symm
      exact (hτ n ω ω' he).2 hn
    · intro hn; exact ⟨ω,rfl,hn⟩
  have hE (n : ℕ) : MeasurableSet (E n) := by
    rw [←hpre n]
    exact MeasurableSet.of_discrete.preimage (hpref n)
  have htau : Measurable τ := by
    intro A hA
    have heq : τ ⁻¹' A = ⋃ n : ℕ, if n ∈ A then E n else ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion]
      constructor
      · intro h; exact ⟨τ ω, by simp [E,h]⟩
      · rintro ⟨n,hn⟩
        by_cases h : n ∈ A
        · simp only [if_pos h] at hn
          change τ ω = n at hn
          simpa [hn] using h
        · simp [h] at hn
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    by_cases h : n ∈ A
    · simpa only [if_pos h] using hE n
    · simp [h]
  let sh : Tape → Tape := fun ω k => ω (k+τ ω)
  have hsh : Measurable sh := by
    apply measurable_pi_lambda
    intro k
    have heval : Measurable (fun x : ℕ × Tape => x.2 (k+x.1)) :=
      measurable_from_prod_countable_right (fun n => measurable_pi_apply (k+n))
    exact heval.comp (htau.prodMk measurable_id)
  change μ.map sh = μ
  ext A hA
  rw [Measure.map_apply hsh hA]
  let ev : ℕ → Set Tape := fun n => E n ∩ (fun ω : Tape => fun k => ω (k+n)) ⁻¹' A
  have hev (n : ℕ) : MeasurableSet (ev n) := (hE n).inter (hA.preimage (by fun_prop))
  have hdis : Pairwise (Function.onFun Disjoint ev) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro ω hn hm
    have hn' : τ ω = n := hn.1
    have hm' : τ ω = m := hm.1
    exact hnm (hn'.symm.trans hm')
  have hdisE : Pairwise (Function.onFun Disjoint E) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro ω hn hm
    exact hnm (hn.symm.trans hm)
  have hUnion : sh ⁻¹' A = ⋃ n, ev n := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, ev, E, Set.mem_inter_iff, Set.mem_setOf_eq, sh]
    constructor
    · intro h; exact ⟨τ ω,rfl,h⟩
    · rintro ⟨n, hn, ha⟩; simpa [hn] using ha
  have hpartition : ⋃ n, E n = Set.univ := by
    ext ω
    simp [E]
  have hmass (n : ℕ) : μ (ev n) = μ (E n) * μ A := by
    have hind := prefix_tail_independent p hp n
    have hm := hind.measure_inter_preimage_eq_mul (F n) A MeasurableSet.of_discrete hA
    have hshift : μ ((fun ω : Tape => fun k => ω (k+n)) ⁻¹' A) = μ A := by
      rw [← Measure.map_apply (by fun_prop) hA, shift_law p hp n]
    change μ (pref n ⁻¹' F n ∩ (fun ω : Tape => fun k => ω (k+n)) ⁻¹' A) = _ at hm
    rw [hpre n, hshift] at hm
    exact hm
  have htotal : (∑' n, μ (E n)) = 1 := by
    rw [← measure_iUnion hdisE hE, hpartition, measure_univ]
  rw [hUnion, measure_iUnion hdis hev]
  simp_rw [hmass]
  rw [ENNReal.tsum_mul_right, htotal, one_mul]
