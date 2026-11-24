-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.nkM_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:56.955048+00:00
-- url     : https://prove2.me/submissions/e8edd1a6-a041-482f-a5ec-780db17171b7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_nkQ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_nkM_eq_nkQ

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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v k : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) :
    nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = (d + v) / 2 := ⟨_, rfl⟩
  have hc : d + v + 1 ≤ 2 * (c + 1) := by omega
  have h2c : 2 * c + 1 ≤ k := by omega
  rw [nkM_eq_nkQ (k := k + 1) (c := c) h𝔭 hH hD hDd hn (by omega) hc (by omega),
    nkM_eq_nkQ (k := k) (c := c) h𝔭 hH hD hDd hn hk hc (by omega)]
  exact nkQ_succ hK h𝔭 hH n h2c
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
