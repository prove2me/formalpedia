-- Prove2me | solution 1 for BosonicLearn.adaptive_scheme_product_povm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T05:29:23.449198+00:00
-- url     : https://prove2.me/submissions/522cfe0d-4b7e-4770-be77-f46e243aa967
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BosonicLearn_AdaptiveScheme
import Definitions.Def_BosonicLearn_sequentialLaw
import Theorems.Thm_BosonicLearn_fockPOVM_compose
import Theorems.Thm_BosonicLearn_fockPOVM_reindex
import Theorems.Thm_BosonicLearn_fockPOVM_postprocess
import Theorems.Thm_BosonicLearn_isDensity_prod
import Theorems.Thm_BosonicLearn_isDensity_reindex
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

/-! ### Product states on the first `k` copies, and appending a copy -/

private def prodState {n N : ℕ} (k : ℕ) (hk : k ≤ N)
    (τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    Matrix (Fin k → Occupation (Fin n)) (Fin k → Occupation (Fin n)) ℂ :=
  Matrix.of fun u v => ∏ t : Fin k, τ (Fin.castLE hk t) (u t) (v t)

private def snocEquiv (α : Type) (k : ℕ) : (Fin k → α) × α ≃ (Fin (k + 1) → α) where
  toFun p := Fin.snoc (α := fun _ => α) p.1 p.2
  invFun u := (Fin.init u, u (Fin.last k))
  left_inv p := by simp [Fin.init_snoc]
  right_inv u := Fin.snoc_init_self u

private lemma measurable_snoc (O : Type) [MeasurableSpace O] (k : ℕ) :
    Measurable fun p : (Fin k → O) × O => (Fin.snoc (α := fun _ => O) p.1 p.2 : Fin (k + 1) → O) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · have h : Measurable fun p : (Fin k → O) × O => p.1 j := (measurable_pi_apply j).comp measurable_fst
    simpa using h

private lemma prodState_succ {n N k : ℕ} (hk1 : k + 1 ≤ N)
    (τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    prodState (k + 1) hk1 τ = fun i j =>
      (fun p q : (Fin k → Occupation (Fin n)) × Occupation (Fin n) =>
        prodState k (Nat.le_of_succ_le hk1) τ p.1 q.1 * τ ⟨k, hk1⟩ p.2 q.2)
        ((snocEquiv (Occupation (Fin n)) k).symm i) ((snocEquiv (Occupation (Fin n)) k).symm j) := by
  funext i j
  simp only [prodState, Matrix.of_apply, snocEquiv, Equiv.coe_fn_symm_mk]
  rw [Fin.prod_univ_castSucc]
  rfl

/-! ### No copies: the one-point system -/

private lemma base_density (n : ℕ) :
    IsDensity (fun (_ _ : Fin 0 → Occupation (Fin n)) => (1 : ℂ)) := by
  classical
  refine ⟨⟨{
    left := fun m => if m = 0 then lp.single 2 (fun i => Fin.elim0 i) 1 else 0
    right := fun m => if m = 0 then lp.single 2 (fun i => Fin.elim0 i) 1 else 0
    summable := summable_of_ne_finset_zero (s := {0}) fun m hm => by
      have : m ≠ 0 := by simpa using hm
      simp [this]
    coefficients := ?_ }⟩, ?_, ?_⟩
  · intro i j
    rw [tsum_eq_single 0 (fun m hm => by simp [hm])]
    have hi : i = fun i => Fin.elim0 i := Subsingleton.elim _ _
    have hj : j = fun i => Fin.elim0 i := Subsingleton.elim _ _
    subst hi hj
    simp
  · intro s z
    have key : ∑ i ∈ s, ∑ j ∈ s, star (z i) * (1 : ℂ) * z j = ((‖∑ i ∈ s, z i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp
    rw [key]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩
  · have h : HasSum (fun _ : Fin 0 → Occupation (Fin n) => ((1 : ℂ)).re) 1 := by
      have := hasSum_fintype (fun _ : Fin 0 → Occupation (Fin n) => ((1 : ℂ)).re)
      simp
    exact ⟨h.summable, h.tsum_eq⟩

private def basePOVM (n : ℕ) (O : Type) [MeasurableSpace O] :
    FockPOVM (Fin 0 → Occupation (Fin n)) (Fin 0 → O) := by
  classical
  exact {
    effect := fun B => if (fun i => Fin.elim0 i) ∈ B then 1 else 0
    effect_form := by
      intro B _ s z
      by_cases hB : (fun i => Fin.elim0 i) ∈ B
      · have key : ∑ i ∈ s, ∑ j ∈ s, star (z i) * (1 : Matrix _ _ ℂ) i j * z j =
            ((∑ i ∈ s, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
            (fun h => (h hi).elim)]
          simp [← Complex.conj_mul']
        simp only [hB, if_true]
        rw [key]
        exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity, by rw [Complex.ofReal_re]⟩
      · simp only [hB, if_false, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]
        exact ⟨rfl, le_rfl, Finset.sum_nonneg fun i _ => by positivity⟩
    effect_univ := by simp
    law := fun _ => Measure.dirac (fun i => Fin.elim0 i)
    law_prob := fun _ _ => inferInstance
    law_born := by
      intro ρ hρ B hB
      have hd : ∀ i : Fin 0 → Occupation (Fin n), i = fun i => Fin.elim0 i := fun i =>
        Subsingleton.elim _ _
      have htr : (ρ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).re = 1 := by
        have h := hρ.2.2.2
        rwa [tsum_eq_single (fun i => Fin.elim0 i) (fun b hb => (hb (hd b)).elim)] at h
      rw [Measure.dirac_apply' _ hB]
      by_cases hmem : (fun i => Fin.elim0 i) ∈ B
      · simp only [hmem, if_true, Set.indicator_of_mem, Pi.one_apply]
        rw [tsum_eq_single (fun i => Fin.elim0 i) (fun b hb => (hb (hd b)).elim),
          tsum_eq_single (fun i => Fin.elim0 i) (fun b hb => (hb (hd b)).elim)]
        simp [htr]
      · simp [hmem] }

/-! ### Induction on the number of rounds -/

private lemma stage {n N : ℕ} {O : Type} [MeasurableSpace O] (S : AdaptiveScheme n N O) :
    ∀ (k : ℕ) (hk : k ≤ N),
      ∃ M : FockPOVM (Fin k → Occupation (Fin n)) (Fin k → O),
        ∀ τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ, (∀ t, IsDensity (τ t)) →
          IsDensity (prodState k hk τ) ∧
            M.law (prodState k hk τ) = sequentialLaw (fun t => S.round (τ t) t) k hk := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨basePOVM n O, fun τ _ => ⟨?_, rfl⟩⟩
    have e : prodState 0 hk τ = fun _ _ => (1 : ℂ) := by
      funext u v
      simp [prodState]
    rw [e]
    exact base_density n
  | succ k ih =>
    intro hk1
    obtain ⟨M, hM⟩ := ih (Nat.le_of_succ_le hk1)
    -- measure the first `k` copies, then the next copy with the POVM chosen from the outcomes
    obtain ⟨M1, hM1⟩ := fockPOVM_compose M (S.povm ⟨k, hk1⟩) (fun τ' => S.round τ' ⟨k, hk1⟩)
      (fun τ' => S.round_markov τ' ⟨k, hk1⟩) (fun τ' hτ' x => S.round_born τ' hτ' ⟨k, hk1⟩ x)
    -- index the `k + 1` copies by tuples, and append the new outcome to the transcript
    obtain ⟨M2, hM2⟩ := fockPOVM_reindex M1 (snocEquiv (Occupation (Fin n)) k)
    obtain ⟨M3, hM3⟩ := fockPOVM_postprocess M2 (Kernel.deterministic _ (measurable_snoc O k))
      inferInstance
    refine ⟨M3, fun τ hτ => ?_⟩
    obtain ⟨hD, hL⟩ := hM τ hτ
    have hprod := isDensity_prod hD (hτ ⟨k, hk1⟩)
    refine ⟨?_, ?_⟩
    · rw [prodState_succ]
      exact isDensity_reindex (snocEquiv (Occupation (Fin n)) k) hprod
    · have hbind : ∀ μ : Measure ((Fin k → O) × O),
          μ.bind (Kernel.deterministic _ (measurable_snoc O k)) =
            μ.map (fun p => (Fin.snoc (α := fun _ => O) p.1 p.2 : Fin (k + 1) → O)) := by
        intro μ
        have hc : (⇑(Kernel.deterministic _ (measurable_snoc O k)) :
            (Fin k → O) × O → Measure (Fin (k + 1) → O)) =
            fun x => Measure.dirac (Fin.snoc (α := fun _ => O) x.1 x.2) := by
          funext x
          exact Kernel.deterministic_apply _ x
        rw [hc]
        exact Measure.bind_dirac_eq_map μ (measurable_snoc O k)
      rw [hM3, prodState_succ, hM2 _ hprod, hM1 _ _ hD (hτ ⟨k, hk1⟩), hL, hbind]
      rfl

theorem solution {n N : ℕ} {O : Type} [MeasurableSpace O] (S : AdaptiveScheme n N O) :
    ∃ M : FockPOVM (Fin N → Occupation (Fin n)) (Fin N → O),
      ∀ τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ, (∀ t, IsDensity (τ t)) →
        M.law (Matrix.of fun u v => ∏ t, τ t (u t) (v t)) =
          sequentialLaw (fun t => S.round (τ t) t) N le_rfl := by
  obtain ⟨M, hM⟩ := stage S N le_rfl
  refine ⟨M, fun τ hτ => ?_⟩
  have h := (hM τ hτ).2
  have e : prodState N le_rfl τ = Matrix.of fun u v => ∏ t, τ t (u t) (v t) := by
    funext u v
    simp [prodState]
  rwa [e] at h
