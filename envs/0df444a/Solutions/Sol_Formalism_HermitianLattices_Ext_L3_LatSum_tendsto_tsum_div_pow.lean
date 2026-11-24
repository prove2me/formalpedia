-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LatSum.tendsto_tsum_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:17.587516+00:00
-- url     : https://prove2.me/submissions/cd9e5abf-25f0-4c6a-b64e-ccfc9204f3e3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LatSum_map_equivFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module MeasureTheory Filter Topology Bornology Pointwise ZLattice
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LatSum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι]
namespace Formalism.HermitianLattices.Ext.L3.LatSum
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : μ (frontier s) = 0) {G : E → ℝ} (hG : Continuous G) :
    Tendsto (fun n : ℕ ↦ (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) / (n : ℝ) ^ finrank ℝ E)
      atTop (𝓝 ((∫ x in s, G x ∂μ) / covolume L μ)) := by
  classical

  let b := Module.Free.chooseBasis ℤ L
  let e := (b.ofZLatticeBasis ℝ L).equivFunL
  let eM := e.toHomeomorph.toMeasurableEquiv
  have heM : ∀ x, eM x = e x := fun _ => rfl
  have hcov : 0 < covolume L μ := ZLattice.covolume_pos L μ
  have hne : ENNReal.ofReal (covolume L μ) ≠ 0 := by simpa using hcov
  have hmap : μ.map eM = ENNReal.ofReal (covolume L μ) • volume := map_equivFun L μ b
  have hL : e '' (L : Set E) =
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    have hspan := b.ofZLatticeBasis_span ℝ L
    have hstep : e '' (L : Set E) = e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) := by
      rw [hspan]
    rw [hstep]
    have hm := Submodule.map_coe (e.toLinearEquiv.toLinearMap.restrictScalars ℤ)
      (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)))
    rw [Submodule.map_span] at hm
    rw [show e '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E) =
      ((e.toLinearEquiv.toLinearMap.restrictScalars ℤ) '' (Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) : Set E))
      from rfl, ← hm, ← Set.range_comp]
    have hfun : ⇑(e.toLinearEquiv.toLinearMap.restrictScalars ℤ) ∘ ⇑(b.ofZLatticeBasis ℝ L) =
        ⇑(Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L)) := by
      funext i
      ext j
      by_cases h : j = i
      · subst h
        simp [e]
      · simp [e, h, Ne.symm h]
    rw [hfun]
  have himg : ∀ n : ℕ, e '' (s ∩ (n : ℝ)⁻¹ • (L : Set E)) =
      e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
        Set (Module.Free.ChooseBasisIndex ℤ L → ℝ)) := by
    intro n
    rw [Set.image_inter e.injective, ← hL]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, (e.map_smul _ a).symm⟩
    · rintro ⟨z, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_ • a, ⟨a, ha, rfl⟩, e.map_smul _ a⟩
  have hsum : ∀ n : ℕ, (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (L : Set E)), G x) =
      ∑' y : ↑(e '' s ∩ (n : ℝ)⁻¹ • (Submodule.span ℤ
        (Set.range (Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L))) :
          Set (Module.Free.ChooseBasisIndex ℤ L → ℝ))), G (e.symm y) := by
    intro n
    rw [← himg n, tsum_image (fun y => G (e.symm y)) e.injective.injOn]
    simp
  have hdim : finrank ℝ E = Fintype.card (Module.Free.ChooseBasisIndex ℤ L) := by
    rw [← ZLattice.rank ℝ L]
    exact Module.finrank_eq_card_chooseBasisIndex ℤ L
  have hpre : eM ⁻¹' (e '' s) = s := Set.preimage_image_eq s e.injective
  have hint : (∫ y in e '' s, G (e.symm y)) = (∫ x in s, G x ∂μ) / covolume L μ := by
    have h1 := setIntegral_map_equiv (μ := μ) eM (fun y => G (e.symm y)) (e '' s)
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hcov.le] at h1
    simp only [heM, ContinuousLinearEquiv.symm_apply_apply] at h1
    rw [← h1, smul_eq_mul, mul_div_cancel_left₀ _ hcov.ne']
  have hfr : volume (frontier (e '' s)) = 0 := by
    have h2 := MeasurableEquiv.map_apply (μ := μ) eM (frontier (e '' s))
    have h3 : eM ⁻¹' frontier (e '' s) = frontier s := by
      have hfe : frontier (e '' s) = e '' frontier s := (e.toHomeomorph.image_frontier s).symm
      rw [hfe]
      exact Set.preimage_image_eq _ e.injective
    rw [h3, hs₃, hmap, Measure.smul_apply, smul_eq_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left hne
  have hlim := tendsto_tsum_div_pow_atTop_integral (e '' s) (fun y => G (e.symm y))
    (hG.comp e.symm.continuous) (e.lipschitz.isBounded_image hs₁)
    (eM.measurableSet_image.2 hs₂) hfr
  rw [hint] at hlim
  refine hlim.congr fun n => ?_
  rw [hsum n, hdim]
end Formalism.HermitianLattices.Ext.L3.LatSum
