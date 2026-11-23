-- Prove2me | solution 1 for Formalism.HN.DualPolygon.dualLat_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:00.331244+00:00
-- url     : https://prove2.me/submissions/b3691385-b930-4a90-af04-934124a3e0e1

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_exists_basis_in
import Theorems.Thm_Formalism_HN_PlaceLattice_exists_denom


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
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution [FiniteDimensional K V] (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    Submodule.span K (dualLat A : Set (Module.Dual K V)) = ⊤ := by
  classical
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  obtain ⟨y, hy, hAy⟩ := Formalism.HN.PlaceLattice.exists_denom e A hA
    (fun x _ => by rw [e.span_eq]; trivial)
  have hyK : (y : K) ≠ 0 := Int.cast_ne_zero.2 hy
  have hmem : ∀ i, ((y : K)) • e.dualBasis i ∈ dualLat A := by
    intro i
    suffices H : ∀ x ∈ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a),
        (((y : K)) • e.dualBasis i) x ∈ Set.range (algebraMap (𝓞 K) K) from
      fun x hx => H x (hAy hx)
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      by_cases h : a = i
      · refine ⟨1, ?_⟩
        simp [LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h, hyK]
      · refine ⟨0, ?_⟩
        simp [LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h]
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨a, ha⟩ := hz
      obtain ⟨c, hc⟩ := hw
      exact ⟨a + c, by rw [map_add, map_add, ha, hc]⟩
    | smul r z _ hz =>
      obtain ⟨a, ha⟩ := hz
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul K r z, map_smul, map_mul, ha, smul_eq_mul]
  rw [eq_top_iff, ← e.dualBasis.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have : e.dualBasis i = ((y : K))⁻¹ • (((y : K)) • e.dualBasis i) := by
    rw [smul_smul, inv_mul_cancel₀ hyK, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))
end Formalism.HN.DualPolygon
