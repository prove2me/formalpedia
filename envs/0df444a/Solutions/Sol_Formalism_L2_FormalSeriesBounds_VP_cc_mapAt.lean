-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_mapAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:47.45594+00:00
-- url     : https://prove2.me/submissions/11f54943-ab46-477a-aee1-00f5ea175b99

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (mapAt ε a i) = 0 := by
  unfold mapAt
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.2)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hb]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · rw [he, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hε i, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 he
    have hmem : s ∈ e.support := Finsupp.mem_support_iff.2 (by simpa using hs)
    have h0 : MvPowerSeries.constantCoeff (e.prod fun s k => a s.2 ^ k) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero hmem
      rw [map_pow, ha s.2, zero_pow (Finsupp.mem_support_iff.1 hmem)]
    rw [h0, smul_zero]
end Formalism.L2.FormalSeriesBounds.VP
