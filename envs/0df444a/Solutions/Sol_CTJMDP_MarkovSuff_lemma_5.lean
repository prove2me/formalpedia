-- Prove2me | solution 1 for CTJMDP.MarkovSuff.lemma_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:43:13.058519+00:00
-- url     : https://prove2.me/submissions/c734efb1-d947-4622-a6dc-2bf99ead06e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting
import Theorems.Thm_CTJMDP_MarkovSuff_lemma_2

open CTJMDP.MarkovSuff MeasureTheory Set
open scoped ENNReal

namespace CTJMDPAuxL5

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

theorem measurable_tn (n : ℕ) : Measurable (fun ω : Traj X => tn ω n) := by
  cases n with
  | zero => simp only [tn]; exact measurable_const
  | succ k => simp only [tn]; fun_prop

theorem measurable_xn (n : ℕ) : Measurable (fun ω : Traj X => xn ω n) := by
  cases n with
  | zero => simp only [xn]; fun_prop
  | succ k => simp only [xn]; fun_prop

theorem measurable_phi_at {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    {t : ℝ} (ht : 0 < t) {B : Set A} (hB : MeasurableSet B) : Measurable (fun z => phi z t B) := by
  have := hphi.measurable B hB
  exact this.comp (f := fun z => ((z, ⟨t, ht⟩) : X × Ioi (0:ℝ))) (by fun_prop)

theorem saMarg_markov {M : Model X A} {phi : X → ℝ → Measure A} (hphi : IsMarkovPolicy M phi)
    (P : Measure (Traj X)) {t : ℝ} (ht : 0 < t) {Z : Set X} (hZ : MeasurableSet Z)
    {B : Set A} (hB : MeasurableSet B) :
    saMarg P (markovPol phi) t Z B = ∫⁻ z in Z, phi z t B ∂(stateMarg P t) := by
  have hg : Measurable (fun z => phi z t B) := measurable_phi_at hphi ht hB
  unfold saMarg expAt stateMarg
  rw [← lintegral_indicator hZ, lintegral_sum_measure]
  congr 1; funext n
  rw [lintegral_map (hg.indicator hZ) (measurable_xn n)]
  congr 1; funext ω
  simp only [markovPol, add_sub_cancel]
  by_cases h : xn ω n ∈ Z <;> simp [h]

end CTJMDPAuxL5

open CTJMDPAuxL5

theorem solution {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [StandardBorelSpace A]
    (M : Model X A) (hM : M.Standing) (hA : M.Assumption21)
    (x : X) (π : Policy X A) (hπ : IsPolicy M π)
    (phi : X → ℝ → Measure A) (hphi : IsMarkovPolicy M phi)
    (Ppi Pphi : Measure (Traj X)) (hPpi : IsLaw M (Measure.dirac x) π Ppi)
    (hPphi : IsLaw M (Measure.dirac x) (markovPol phi) Pphi)
    (h16 : Disintegrates Ppi π phi) :
    (∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
      saMarg Pphi (markovPol phi) t Z B ≤ saMarg Ppi π t Z B) ∧
    (∀ s : ℝ, 0 < s → stateMarg Pphi s univ = 1 →
      ∀ t ∈ Ioc (0 : ℝ) s, ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B) ∧
    ((∀ t : ℝ, 0 < t → stateMarg Pphi t univ = 1) →
      ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B) := by
  obtain ⟨-, h2ii, h2iii, h2iv⟩ :=
    lemma_2 M hM hA x π hπ phi hphi Ppi Pphi hPpi hPphi h16
  -- (51): both marginals are integrals of `ϕ(B | z, t)` against the state marginals
  have h51 : ∀ t : ℝ, 0 < t → ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
      saMarg Pphi (markovPol phi) t Z B = ∫⁻ z in Z, phi z t B ∂(stateMarg Pphi t) ∧
      saMarg Ppi π t Z B = ∫⁻ z in Z, phi z t B ∂(stateMarg Ppi t) :=
    fun t ht Z B hZ hB => ⟨saMarg_markov hphi Pphi ht hZ hB, h16 t ht Z B hZ hB⟩
  have heq : ∀ t : ℝ, 0 < t → (∀ Z : Set X, MeasurableSet Z → stateMarg Pphi t Z = stateMarg Ppi t Z) →
      ∀ (Z : Set X) (B : Set A), MeasurableSet Z → MeasurableSet B →
        saMarg Pphi (markovPol phi) t Z B = saMarg Ppi π t Z B := by
    intro t ht hm Z B hZ hB
    rw [(h51 t ht Z B hZ hB).1, (h51 t ht Z B hZ hB).2, Measure.ext hm]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht Z B hZ hB
    rw [(h51 t ht Z B hZ hB).1, (h51 t ht Z B hZ hB).2]
    exact lintegral_mono' (Measure.restrict_mono le_rfl
      (Measure.le_iff.2 fun Z' hZ' => h2ii t ht Z' hZ')) le_rfl
  · intro s hs hs1 t ht Z B hZ hB
    exact heq t ht.1 (fun Z' hZ' => h2iii s hs hs1 t ht Z' hZ') Z B hZ hB
  · intro hall t ht Z B hZ hB
    exact heq t ht (fun Z' hZ' => h2iv hall t ht Z' hZ') Z B hZ hB
