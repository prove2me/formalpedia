-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.Qc_piQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:21.74925+00:00
-- url     : https://prove2.me/submissions/374623d9-98d8-49b2-adb4-bc379f65afee

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_Qc_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_exists_liftv

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K))
    (x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ↔ Qc 𝔭 (k + 1) c H x := by
  obtain ⟨y, rfl⟩ := exists_liftv 𝔭 (k + 1) x
  rw [Qc_mk (by omega) H y]
  exact Qc_mk hck H y
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
