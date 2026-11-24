-- Prove2me | solution 1 for Formalism.HN.slopeIneqMean_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:01.681455+00:00
-- url     : https://prove2.me/submissions/ab6c5859-f580-41a3-9720-d425b4cee4d2

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_norm_sq_realize
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_normAt_map_le
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_opNormAt_smul
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_opNormAt_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open PlaceOperatorNorms
namespace Formalism.HN
theorem _root_.solution (h1 : Twist) (h2 : PlLat) (h3 : SlopeIneq.{0, 0, 0, 0, 0}) :
    SlopeIneqMean := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A hA hφA
  have hφ : φ ≠ 0 := by
    rintro rfl
    apply hφA
    rw [LinearMap.restrictScalars_zero, Submodule.map_zero]
  have hpos : ∀ v, 0 < opNormAt b X b' X' v φ := fun v => opNormAt_pos b X b' X' hX hX' v φ hφ
  have hf : (nPl K : ℝ) ≠ 0 := by
    unfold nPl
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = htMap b X b' X' φ / 2 := ⟨_, rfl⟩
  have hs' : s = (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ) := by
    rw [hs, htMap, Finset.sum_congr rfl (fun v _ => Real.log_pow (opNormAt b X b' X' v φ) 2),
      ← Finset.mul_sum]
    push_cast
    ring
  obtain ⟨c, hc_def⟩ : ∃ c : InfinitePlace K → ℝ,
      c = fun v => opNormAt b X b' X' v φ * Real.exp (-s) := ⟨_, rfl⟩
  have hc : ∀ v, 0 < c v := fun v => by
    rw [hc_def]
    exact mul_pos (hpos v) (Real.exp_pos _)
  have ht0 : (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) = 0 := by
    have hl : ∀ v, Real.log (c v) = Real.log (opNormAt b X b' X' v φ) - s := fun v => by
      rw [hc_def]
      dsimp only
      rw [Real.log_mul (hpos v).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    simp only [hl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_sub, ← hs']
    have hfs : (1 / (nPl K : ℝ)) * ((Fintype.card (InfinitePlace K) : ℝ) * s) = s := by
      unfold nPl at hf ⊢
      field_simp
    rw [hfs, sub_self]
  obtain ⟨X'', hX''⟩ : ∃ X'' : InfinitePlace K → Matrix κ κ ℂ,
      X'' = fun v => ((c v : ℂ)) • X' v := ⟨_, rfl⟩
  have hdet'' : ∀ v, IsUnit (X'' v).det := fun v => by
    rw [hX'']
    dsimp only
    rw [Matrix.det_smul]
    exact ((Complex.ofReal_ne_zero.mpr (hc v).ne').isUnit.pow _).mul (hX' v)
  have htw : ∀ N : Submodule (𝓞 K) W, N.FG → N ≠ ⊥ →
      muMax (Formalism.HermitianLatticesTheory.realize b' X'') N = muMax (Formalism.HermitianLatticesTheory.realize b' X') N ∧
      muMin (Formalism.HermitianLatticesTheory.realize b' X'') N = muMin (Formalism.HermitianLatticesTheory.realize b' X') N := by
    intro N hN hN0
    have := (h1 K W κ b' X' c hX' hc N hN).2.1 hN0
    rw [ht0, add_zero, add_zero] at this
    rw [hX'']
    exact this
  have hC : 0 < Real.exp s := Real.exp_pos s
  have hbound : ∀ x : V,
      ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ≤ Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
    intro x
    have hpl : ∀ v, Formalism.HermitianLatticesTheory.normAt b' X'' v (φ x) ≤ Real.exp s * Formalism.HermitianLatticesTheory.normAt b X v x := by
      intro v
      have hop : opNormAt b X b' X'' v φ = Real.exp s := by
        rw [hX'', opNormAt_smul b X b' X' hX' c hc v φ, hc_def]
        dsimp only
        rw [mul_inv, Real.exp_neg, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hpos v).ne',
          one_mul]
      calc Formalism.HermitianLatticesTheory.normAt b' X'' v (φ x)
          ≤ opNormAt b X b' X'' v φ * Formalism.HermitianLatticesTheory.normAt b X v x := normAt_map_le b X b' X'' hX v φ x
        _ = Real.exp s * Formalism.HermitianLatticesTheory.normAt b X v x := by rw [hop]
    have hsq : ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ^ 2 ≤
        (Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖) ^ 2 := by
      rw [mul_pow, norm_sq_realize, norm_sq_realize, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpl v) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hAlat := (h2 K V ι b X hX A hA).1
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    apply hφA
    exact Submodule.map_bot _
  have key : ∀ M : Submodule (𝓞 K) W, M.FG → A.map (φ.restrictScalars (𝓞 K)) ≤ M →
      (muMin (Formalism.HermitianLatticesTheory.realize b X) A - s ≤
          muMin (Formalism.HermitianLatticesTheory.realize b' X'') (A.map (φ.restrictScalars (𝓞 K))) ∧
        muMin (Formalism.HermitianLatticesTheory.realize b X) A ≤ muMax (Formalism.HermitianLatticesTheory.realize b' X'') M + s) ∧
      (Set.InjOn φ (A : Set V) →
        muMax (Formalism.HermitianLatticesTheory.realize b X) A ≤ muMax (Formalism.HermitianLatticesTheory.realize b' X'') M + s) := by
    intro M hM hAM
    have hMlat := (h2 K W κ b' X'' hdet'' M hM).1
    have hmem : ∀ x : A, (φ.restrictScalars (𝓞 K)).domRestrict A x ∈ M := fun x =>
      hAM (Submodule.mem_map_of_mem x.2)
    let ψ : A →ₗ[𝓞 K] M := LinearMap.codRestrict M ((φ.restrictScalars (𝓞 K)).domRestrict A) hmem
    have hψ : ∀ x : A, ((ψ x : M) : W) = φ x := fun x => rfl
    have hS := h3 (𝓞 K) V W _ _ (Formalism.HermitianLatticesTheory.realize b X) (Formalism.HermitianLatticesTheory.realize b' X'') A M hAlat hMlat
      ψ (Real.exp s) hC (fun x => by rw [hψ]; exact hbound x)
    rw [Real.log_exp] at hS
    have hrange : (LinearMap.range ψ).map M.subtype = A.map (φ.restrictScalars (𝓞 K)) := by
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply]
      constructor
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hψ0 : ψ ≠ 0 := by
      obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hφA
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      intro h
      apply hy0
      have := congrArg (fun g : A →ₗ[𝓞 K] M => ((g ⟨x, hx⟩ : M) : W)) h
      simpa [hψ] using this
    refine ⟨?_, fun hinj => hS.2 ?_ hA0⟩
    · have := (hS.1 hψ0).1
      rw [hrange] at this
      exact ⟨this, (hS.1 hψ0).2⟩
    · intro x y hxy
      apply Subtype.ext
      apply hinj x.2 y.2
      have := congrArg (fun z : M => (z : W)) hxy
      simpa [hψ] using this
  have hφA_fg : (A.map (φ.restrictScalars (𝓞 K))).FG := hA.map _
  obtain ⟨⟨k1, -⟩, -⟩ := key _ hφA_fg le_rfl
  have htφA := htw _ hφA_fg hφA
  rw [htφA.2] at k1
  refine ⟨?_, fun B hB hAB => ?_⟩
  · unfold muMinDef
    linarith
  · have hB0 : B ≠ ⊥ := fun h => hφA (le_bot_iff.mp (h ▸ hAB))
    obtain ⟨⟨-, k2⟩, k3⟩ := key B hB hAB
    have htB := htw B hB hB0
    rw [htB.1] at k2 k3
    refine ⟨?_, fun hinj => ?_⟩
    · unfold muMinDef muMaxDef
      linarith
    · have := k3 hinj
      unfold muMaxDef
      linarith
end Formalism.HN
