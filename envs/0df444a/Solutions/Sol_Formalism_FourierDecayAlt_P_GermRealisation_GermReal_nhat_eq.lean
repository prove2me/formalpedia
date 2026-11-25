-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermRealisation.GermReal.nhat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:43.834063+00:00
-- url     : https://prove2.me/submissions/76117d82-7193-4917-8dc2-3314f467316d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocTail
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfRealised

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
attribute [instance] GermReal.nag GermReal.ips GermReal.cs
namespace Formalism.FourierDecayAlt.P.GermRealisation
namespace GermReal
theorem _root_.solution {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : GermReal S v ε b s a Y) {h h' : C.LPt} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ : ℂ) :
    Nhat s R.β R.bt σ h h' = KB.hatB S v ε b s a σ h h' := by
  have hdl : ((KB.dlB S b s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr R.hdl
  have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    rw [ae_iff]; simp
  unfold KB.hatB Nhat
  have hae : (fun c => KB.gN S v ε (b + s - 1) a (h ++ [(s, c)]) (h' ++ [(s, c)]) * KB.psiL S σ c)
      =ᵐ[volume] fun c => ((KB.dlB S b s : ℝ) : ℂ) *
        (G.psi R.β (σ * c) • ⟪bz s (R.bt h) c, bz s (R.bt h') c⟫_ℂ) := by
    filter_upwards [h0] with c hc
    have hd := R.dens h hh h' hh' c hc
    unfold gDens at hd
    rw [hd, ← R.hpsi σ c, smul_eq_mul]
    ring
  rw [integral_congr_ae hae, integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hdl, one_mul]
end GermReal
end Formalism.FourierDecayAlt.P.GermRealisation
