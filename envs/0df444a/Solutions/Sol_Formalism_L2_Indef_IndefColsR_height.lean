-- Prove2me | solution 1 for Formalism.L2.Indef.IndefColsR.height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:48.972283+00:00
-- url     : https://prove2.me/submissions/5f526394-4a10-4b79-8ff8-d7250ae6b653

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_ColData_invZ_B
import Theorems.Thm_P2M_Formalism_L2_Indef_ColData_invZ___f21f866b969d
import Theorems.Thm_Formalism_L2_Indef_ColData_invZ_sE
import Theorems.Thm_Formalism_L2_Indef_IndefColsR_dQ_eq
import Theorems.Thm_Formalism_L2_Indef_IndefColsR_Qpart_base
import Theorems.Thm_Formalism_L2_Indef_IndefColsR_log_eigenvalue_sum_le_min
import Theorems.Thm_Formalism_L2_Indef_IndefCols_log_eigenvalue_sum_le_min
import Theorems.Thm_Formalism_L2_Indef_IndefRows_Qpart_base
import Theorems.Thm_Formalism_L2_Indef_IndefRows_dQ_eq
import Theorems.Thm_Formalism_L2_Indef_isUnit_det_of_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Indef.ColData.invZ_B
attribute [local simp] Formalism.L2.Indef.ColData.invZ_ζ
attribute [local simp] Formalism.L2.Indef.ColData.invZ_sE

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)
namespace Formalism.L2.Indef.IndefColsR
theorem _root_.solution (hH : HeightBoundConstant) [Nonempty Bs.Ix] (wf : Df.WF) (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det)
    (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v) :
    Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
              (Formalism.HN.dualFrame S.XE) (S.col.B u) ≤
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j - meanLog S.κ := by
  have hQ := S.dQ_eq
  have hfr := S.frames
  have hc := S.l1c
  have hb := S.l1b
  have hmin := S.log_eigenvalue_sum_le_min
  have hsc : ∀ v p, IsScalarOn (Df.XQ Bs.μ0) S.XE v (S.ι Bs.μ0) (Df.Qp Bs.μ0 p)
      (S.κ v * ∏ j, S.lam j Bs.μ0 p v) := fun v p => by
    rw [← S.Qpart_base p]; exact hc.2.2.2 Bs.μ0 v (Or.inl rfl) p
  obtain ⟨⟨μ, Tw, D, XE, Ep, ι, dW, XW, Wp, M, θ, κ, lam, err0⟩, _p1, _g0, _g1, _g2, _g3, _g5, ⟨B, ζ, sE⟩, _g6, _g7⟩ := S
  obtain ⟨HH, nHH, iHH, Pu, Rw⟩ := Sp
  obtain ⟨Mem, a, Xc, Pt⟩ := Dc
  obtain ⟨nV, HV, Mt, dQ, Pq, XQ, Qp, dZ, HT, XT, Tl, Zp⟩ := Df
  dsimp only at hQ hfr hc hb hmin hsc hXc hne X0 hX0 hpU u
  obtain rfl : dQ = fun _ => D := funext hQ
  have H := (hH K (nV Bs.μ0) D 0 (fun _ => a u) (fun _ => Xc u) (fun _ => hXc) (fun j => j.elim0) (HV Bs.μ0) X0 hX0
    (Pq Bs.μ0) (wf.Pq_surj _) (XQ Bs.μ0) (wf.XQ_quot _) XE hfr (ι Bs.μ0) (isUnit_det_of_bij _ (hc.1 _))
    Bs.Ix Bs.J (Qp Bs.μ0) wf.Qp_top κ (fun j p v => lam j Bs.μ0 p v) (fun j p v => lam j Bs.μ0 p v)
    hc.2.1 (fun j p v => hc.2.2.1 j _ p v) (fun _ _ _ => le_rfl)
    hsc (Pt u Bs.μ0) (B u)
    (fun φ F => by
      have h1 := hb.1 u Bs.μ0 φ F
      rw [hb.2.1 u, one_mul] at h1
      rw [← h1]
      show _ = Pt u Bs.μ0 ((1 : Matrix (Fin (a u)) (Fin (a u)) K).mulVec φ) F
      rw [Matrix.one_mulVec])
    hne pU (fun j => j.elim0) hpU (fun j => j.elim0)).2
  have hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    exact_mod_cast this
  have h2 : ∑ j, N.l6 j ≤ (1 / (Formalism.HN.nPl K : ℝ)) *
      ∑ v, minOver (fun p => ∑ j, Real.log (lam j Bs.μ0 p v)) := by
    have h3 : ∑ _v : InfinitePlace K, ∑ j, N.l6 j ≤
        ∑ v, minOver (fun p => ∑ j, Real.log (lam j Bs.μ0 p v)) := Finset.sum_le_sum fun v _ => hmin v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    rw [one_div, le_inv_mul_iff₀ hn]
    exact h3
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at H
  linarith [H, h2]
end Formalism.L2.Indef.IndefColsR
