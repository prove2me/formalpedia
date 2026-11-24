-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.ofNbr_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:53:50.413009+00:00
-- url     : https://prove2.me/submissions/abca17f6-521e-4668-9347-16f12be5d5a1

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_LocOp_adjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}
namespace Formalism.L2.Col.LocOp
theorem _root_.solution (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (nb : S'.D → Finset S.D) (nb' : S.D → Finset S'.D) (T : S.V →ₗ[K] S'.V) (T' : S'.V →ₗ[K] S.V)
    (hn : ∀ g d' d, (e.symm : S'.G →* S.G) g • d ∈ nb (g • d') ↔ d ∈ nb d')
    (hT : ∀ g x, T (S.ρ ((e.symm : S'.G →* S.G) g) x) = S'.ρ g (T x))
    (hn' : ∀ g d d', (e : S.G →* S'.G) g • d' ∈ nb' (g • d) ↔ d' ∈ nb' d)
    (hT' : ∀ g x, T' (S'.ρ ((e : S.G →* S'.G) g) x) = S.ρ g (T' x))
    (htr : ∀ d d', d ∈ nb d' ↔ d' ∈ nb' d) (h0 : T = 0 ↔ T' = 0)
    (hadj : ∀ x y, S'.pair (T x) y = S.pair x (T' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' ((ofNbr (e.symm : S'.G →* S.G) nb T hn hT).op φ) ψ =
      S.ipOf h s φ ((ofNbr (e : S.G →* S'.G) nb' T' hn' hT').op ψ) := by
  classical
  have hk : ∀ d d', (ofNbr (e.symm : S'.G →* S.G) nb T hn hT).ker d' d = if d ∈ nb d' then T else 0 := by
    intro d d'
    show Finsupp.indicator (nb d') (fun _ _ => T) d = _
    rw [Finsupp.indicator_apply]
    by_cases hd : d ∈ nb d'
    · rw [dif_pos hd, if_pos hd]
    · rw [dif_neg hd, if_neg hd]
  have hk' : ∀ d d', (ofNbr (e : S.G →* S'.G) nb' T' hn' hT').ker d d' = if d ∈ nb d' then T' else 0 := by
    intro d d'
    show Finsupp.indicator (nb' d) (fun _ _ => T') d' = _
    rw [Finsupp.indicator_apply]
    by_cases hd : d ∈ nb d'
    · rw [dif_pos ((htr d d').mp hd), if_pos hd]
    · rw [dif_neg (fun H => hd ((htr d d').mpr H)), if_neg hd]
  refine adjoint _ _ h h' e (fun _ => rfl) ?_ ?_ s s' φ ψ
  · intro d d'
    rw [hk, hk']
    by_cases hd : d ∈ nb d'
    · rw [if_pos hd, if_pos hd, h0]
    · rw [if_neg hd, if_neg hd]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro d d' x y
    rw [hk, hk']
    by_cases hd : d ∈ nb d'
    · rw [if_pos hd, if_pos hd, hadj]
    · rw [if_neg hd, if_neg hd]
      simp
end Formalism.L2.Col.LocOp
