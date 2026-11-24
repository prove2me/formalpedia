-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.fm_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:20.775317+00:00
-- url     : https://prove2.me/submissions/b1cf25c1-53bd-42cb-aff8-370b8ecf379c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
theorem _root_.solution (hF : IsFixF K F) (H : Matrix m m (𝓞 K)) (a : 𝓞 F) (y : m → 𝓞 K) :
    fm H (fun i => ι a * y i) (fun i => ι a * y i) = ι (a * a) * fm H y y := by
  have hs : ∀ i, star (ι a * y i) = ι a * star (y i) := fun i => by
    rw [star_mul', idealPowerSpanBounds.star_def (ι a), conjO_map hF]
  simp only [fm, dotProduct, Matrix.mulVec, Pi.star_apply, hs, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
