-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.nkM_eq_nkQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:37.291804+00:00
-- url     : https://prove2.me/submissions/85289372-2a36-4ced-9c07-5b2f322f6265

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_Qc_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_exists_liftv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_mk_fm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_exists_notMem_of_sol

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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {H : Matrix m m (𝓞 K)}
    (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v c k : ℕ} (hDd : D ∉ 𝔭 ^ (d + 1))
    (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) (hc : d + v + 1 ≤ 2 * (c + 1)) (hck : c + 1 ≤ k) :
    nkM 𝔭 k H n = nkQ 𝔭 k c H n := by
  unfold nkM nkQ
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
  constructor
  · intro hx
    refine ⟨?_, hx⟩
    obtain ⟨y, rfl⟩ := exists_liftv 𝔭 k x
    rw [Qc_mk hck H y]
    rw [mk_fm] at hx
    have hy : fm H y y - ι n ∈ extP K 𝔭 ^ k := Ideal.Quotient.eq.mp hx
    exact exists_notMem_of_sol h𝔭 hH hD hDd hn hk hc hy
  · exact fun h => h.2
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
