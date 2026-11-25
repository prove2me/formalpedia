-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.map_nabValN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:10:41.064351+00:00
-- url     : https://prove2.me/submissions/c841617e-33e4-4039-9aa2-3135dbc4a916

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_constantCoeff_eval_single
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_DpolyN
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_MapFB_map_expS__5faa65c8ae0f
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_constantCoeff_eval_pair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.MapFB
theorem _root_.solution [Algebra ℚ K] [Algebra ℚ C] {O : Type} [CommRing O] [StarRing O]
    (B : FB K d O) (B' : FB C d O) (hF : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j))
    (hA : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)) (h : PS K 2 d)
    (hh : constantCoeff h = 0) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {ι : Type} [Fintype ι]
    (cp : ι → Fin n) (u : ι → Fin d → K) (P : MvPolynomial ι K) :
    nabValN B' C (MvPowerSeries.map φ h) w0 m (MvPowerSeries.map φ f) cp (fun l i => φ (u l i))
        (MvPolynomial.map φ P) = φ (nabValN B K h w0 m f cp u P) := by
  unfold nabValN
  rw [← constantCoeff_map]
  congr 1
  have e1 : B.FK K = B.G.F := rfl
  have e2 : B'.FK C = fun j => MvPowerSeries.map φ (B.G.F j) := funext hF
  have eA : mpt φ (B.A.act w0) = B'.actK C w0 := by
    funext j; exact (hA w0 j).symm
  have eK : B.actK K w0 = B.A.act w0 := rfl
  have p0 : ∀ i, constantCoeff (pt K d (0 : Fin 1) i) = 0 := cc_pt (R := K) (d := d) 0
  have q0 : ∀ i, constantCoeff (comp1 (B.A.act w0) (pt K d (0 : Fin 1)) i) = 0 :=
    cc_comp1 (B.A.act w0) (B.A.const w0) (pt K d (0 : Fin 1)) p0
  have hL : MvPowerSeries.map φ (B.hL K h w0) = B'.hL C (MvPowerSeries.map φ h) w0 := by
    unfold FB.hL
    rw [eK, map_ev2 φ (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, mpt_pt,
      mpt_comp1 φ (B.A.act w0) (pt K d 0) p0, mpt_pt, eA]
  have hcL : constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    rw [eK, constantCoeff_eval_pair (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, hh]
  have hcb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := fun b => by
    rw [constantCoeff_eval_single (pt K d b) (cc_pt (R := K) (d := d) b), hcL]
  have hcs : constantCoeff ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_sum, Finset.sum_eq_zero fun b _ => hcb b, smul_zero]
  have hsum : ∑ b : Fin n, MvPowerSeries.map φ (ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![pt C d b] (B'.hL C (MvPowerSeries.map φ h) w0) :=
    Finset.sum_congr rfl fun b _ => by
      rw [map_ev1 φ (pt K d b) (cc_pt (R := K) (d := d) b), mpt_pt, hL]
  rw [e1, e2, map_DpolyN, map_mul, map_expS' φ _ hcs, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    map_nsmul, map_sum, hsum]
end Formalism.L2.FormalSeriesBounds.MapFB
