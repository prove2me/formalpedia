-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.mk_fm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:22.572986+00:00
-- url     : https://prove2.me/submissions/89a45de5-4d5b-4e26-b41c-c098ee768b5f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (x y : m → 𝓞 K) :
    fm (H.map (mkk K 𝔭 k)) (fun i => mkk K 𝔭 k (x i)) (fun i => mkk K 𝔭 k (y i)) =
      mkk K 𝔭 k (fm H x y) := by
  have hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i) := by
    funext i
    exact idealPowerSpanBounds.star_mk 𝔭 k (x i)
  have hv : H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i)) =
      fun i => mkk K 𝔭 k ((H *ᵥ y) i) := by
    funext i
    exact (RingHom.map_mulVec (mkk K 𝔭 k) H y i).symm
  show star (fun i => mkk K 𝔭 k (x i)) ⬝ᵥ (H.map (mkk K 𝔭 k) *ᵥ (fun i => mkk K 𝔭 k (y i))) =
    mkk K 𝔭 k (star x ⬝ᵥ (H *ᵥ y))
  rw [hs, hv, RingHom.map_dotProduct]
  rfl
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
