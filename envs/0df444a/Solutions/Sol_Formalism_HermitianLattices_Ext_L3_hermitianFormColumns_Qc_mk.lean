-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.Qc_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:16.314832+00:00
-- url     : https://prove2.me/submissions/d8b1f7be-d8b4-454c-9e53-06f318fc59f0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mk_mem_idQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K)) (x : m → 𝓞 K) :
    Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) ↔ ∃ j, (star x ᵥ* H) j ∉ extP K 𝔭 ^ (c + 1) := by
  have e : ∀ j, (star (fun i => mkk K 𝔭 k (x i)) ᵥ* H.map (mkk K 𝔭 k)) j =
      mkk K 𝔭 k ((star x ᵥ* H) j) := by
    intro j
    have hs : star (fun i => mkk K 𝔭 k (x i)) = fun i => mkk K 𝔭 k (star x i) := by
      funext i
      exact idealPowerSpanBounds.star_mk 𝔭 k (x i)
    rw [hs]
    exact (RingHom.map_vecMul (mkk K 𝔭 k) H (star x) j).symm
  unfold Qc
  simp only [e, mk_mem_idQ hck]
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
