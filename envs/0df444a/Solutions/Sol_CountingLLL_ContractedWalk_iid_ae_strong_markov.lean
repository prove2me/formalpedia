-- Prove2me | solution 1 for CountingLLL.ContractedWalk.iid_ae_strong_markov
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:57:24.188892+00:00
-- url     : https://prove2.me/submissions/25cd2d55-9580-4a56-80e0-332054b20fad

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


theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) (τ : Tape → Option ℕ) (R : Tape → ℕ)
    (hτ : ∀ n ω ω', (∀ k < n, ω k = ω' k) → (τ ω = some n ↔ τ ω' = some n))
    (hR : ∀ n ω ω', (∀ k < n, ω k = ω' k) → τ ω = some n → R ω = R ω')
    (hfin : ∀ᵐ ω ∂tapeLaw p, τ ω ≠ none) :
    IndepFun R (fun ω k => ω (k+(τ ω).getD 0)) (tapeLaw p) ∧
    (∀ A : Set Tape, MeasurableSet A → tapeLaw p ((fun ω : Tape => fun k => ω (k+(τ ω).getD 0)) ⁻¹' A) = tapeLaw p A) := by
  classical
  letI : IsProbabilityMeasure (bitLaw p) := bitLaw_probability' p hp
  let μ := tapeLaw p
  letI : IsProbabilityMeasure μ := by dsimp [μ,tapeLaw]; infer_instance
  have hmassAll (B : Set ℕ) (A : Set Tape) (hA : MeasurableSet A) :
      μ (R ⁻¹' B ∩ (fun ω : Tape => fun k => ω (k+(τ ω).getD 0)) ⁻¹' A) = μ (R ⁻¹' B) * μ A := by
    let pref : (n : ℕ) → Tape → (Fin n → Bool) := fun n ω j => ω j.val
    let L : ℕ → Set Tape := fun n => {ω | τ ω = some n ∧ R ω ∈ B}
    let F : (n : ℕ) → Set (Fin n → Bool) := fun n => {x | ∃ ω : Tape, pref n ω = x ∧ τ ω = some n ∧ R ω ∈ B}
    have hpref (n : ℕ) : Measurable (pref n) := measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
    have hpre (n : ℕ) : pref n ⁻¹' F n = L n := by
      ext ω
      constructor
      · rintro ⟨ω', heq, hn, hval⟩
        have he : ∀ k < n, ω k = ω' k := by intro k hk; exact (congrFun heq ⟨k,hk⟩).symm
        have hnow : τ ω = some n := (hτ n ω ω' he).2 hn
        exact ⟨hnow, by rw [hR n ω ω' he hnow]; exact hval⟩
      · rintro ⟨hn,hval⟩; exact ⟨ω,rfl,hn,hval⟩
    have hL (n : ℕ) : MeasurableSet (L n) := by
      rw [←hpre n]
      exact MeasurableSet.of_discrete.preimage (hpref n)
    let ev : ℕ → Set Tape := fun n => L n ∩ (fun ω : Tape => fun k => ω (k+n)) ⁻¹' A
    have hev (n : ℕ) : MeasurableSet (ev n) := (hL n).inter (hA.preimage (by fun_prop))
    have hdis : Pairwise (Function.onFun Disjoint ev) := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      intro ω hn hm
      have hn' : τ ω = some n := hn.1.1
      have hm' : τ ω = some m := hm.1.1
      exact hnm (Option.some.inj (hn'.symm.trans hm'))
    have hdisL : Pairwise (Function.onFun Disjoint L) := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      intro ω hn hm
      exact hnm (Option.some.inj (hn.1.symm.trans hm.1))
    have hUnion : ((R ⁻¹' B ∩ (fun ω : Tape => fun k => ω (k+(τ ω).getD 0)) ⁻¹' A) : Set Tape) =ᵐ[μ] (⋃ n, ev n) := by
      filter_upwards [hfin] with ω hω
      cases he : τ ω with
      | none => exact False.elim (hω he)
      | some n =>
        apply propext
        change (R ω ∈ B ∧ (fun k => ω (k+(τ ω).getD 0)) ∈ A) ↔ ω ∈ ⋃ n, ev n
        simp only [Set.mem_iUnion, ev, L, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
        simp [he]
    have hpartition : (⋃ n, L n) =ᵐ[μ] R ⁻¹' B := by
      filter_upwards [hfin] with ω hω
      cases he : τ ω with
      | none => exact False.elim (hω he)
      | some n =>
        apply propext
        change (ω ∈ ⋃ n, L n) ↔ R ω ∈ B
        simp [L,he]
    have hmass (n : ℕ) : μ (ev n) = μ (L n) * μ A := by
      have hind := prefix_tail_independent p hp n
      have hm := hind.measure_inter_preimage_eq_mul (F n) A MeasurableSet.of_discrete hA
      have hshift : μ ((fun ω : Tape => fun k => ω (k+n)) ⁻¹' A) = μ A := by
        rw [← Measure.map_apply (by fun_prop) hA, shift_law p hp n]
      change μ (pref n ⁻¹' F n ∩ (fun ω : Tape => fun k => ω (k+n)) ⁻¹' A) = _ at hm
      rw [hpre n, hshift] at hm
      exact hm
    have htotal : (∑' n, μ (L n)) = μ (R ⁻¹' B) := by
      rw [← measure_iUnion hdisL hL]
      exact measure_congr hpartition
    rw [measure_congr hUnion, measure_iUnion hdis hev]
    simp_rw [hmass]
    rw [ENNReal.tsum_mul_right, htotal]
  have htail (A : Set Tape) (hA : MeasurableSet A) : μ ((fun ω : Tape => fun k => ω (k+(τ ω).getD 0)) ⁻¹' A) = μ A := by
    have hh := hmassAll Set.univ A hA
    simpa only [Set.preimage_univ, Set.univ_inter, measure_univ, one_mul] using hh
  constructor
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro B A hB hA
    rw [htail A hA]
    exact hmassAll B A hA
  · exact htail
