-- Prove2me | solution 1 for Formalism.L2.PjFree.reFrame_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:00.591294+00:00
-- url     : https://prove2.me/submissions/a54c11cf-fa54-4792-b828-89acd1bbc416

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Theorems.Thm_Formalism_L2_PjFree_isCombAt_unique
import Theorems.Thm_Formalism_L2_PjFree_isCombAt_exists
import Theorems.Thm_Formalism_L2_PjFree_isCombAt_single
import Theorems.Thm_P2M_Formalism_L2_Pj_iwasawa__f83cbdce79a0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace Formalism.L2.PjFree
theorem _root_.solution (hT : TanLin Xo) (hR : IntRebase Xo c) : ReFrame Xo c := by
  intro T io
  let _ := io.toAlgebra
  intro y0 z hx
  have tz : ∀ τ i, IsTanAt y0.1.x (z.u τ i) := fun τ i => by rw [← hx]; exact z.tan τ i
  have ty : ∀ τ i, IsTanAt z.x (y0.1.u τ i) := fun τ i => by rw [hx]; exact y0.1.tan τ i
  have hA : ∀ τ i, ∃ a : Fin (Dw.mult τ) → T.Fr, IsCombAt y0.1.x (y0.1.u τ) a (z.u τ i) :=
    fun τ i => (y0.1.basis τ (z.u τ i) (tz τ i) (z.eig τ i)).exists
  choose a ha using hA
  have hB : ∀ τ j, ∃ b : Fin (Dw.mult τ) → T.Fr, IsCombAt z.x (z.u τ) b (y0.1.u τ j) :=
    fun τ j => (z.basis τ (y0.1.u τ j) (ty τ j) (y0.1.eig τ j)).exists
  choose b hb using hB
  let A : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr := fun τ => Matrix.of fun j i => a τ i j
  let Bm : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr := fun τ => Matrix.of fun j i => b τ i j
  have hAB : ∀ τ, A τ * Bm τ = 1 := by
    intro τ
    ext j' i'
    have hb' : IsCombAt y0.1.x (z.u τ) (b τ i') (y0.1.u τ i') := by rw [← hx]; exact hb τ i'
    have hc := hT T.Fr y0.1.x (y0.1.u τ) (y0.1.tan τ) (z.u τ) (A τ) (b τ i') (y0.1.u τ i')
      (fun i => ha τ i) hb'
    have hu := isCombAt_single (y0.1.tan τ) i'
    have heq := (y0.1.basis τ (y0.1.u τ i') (y0.1.tan τ i') (y0.1.eig τ i')).unique hc hu
    have h1 := congrFun heq j'
    simp only [Matrix.mulVec, dotProduct, A, Bm, Matrix.of_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, Bm, Matrix.of_apply]
    rw [h1, Pi.single_apply]
  have hdet : ∀ τ, (A τ).det ≠ 0 := fun τ h => by
    have h2 := congrArg Matrix.det (hAB τ)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  choose k N hk hN hNd hAN using fun τ => iwasawa' (V := T.V) (A τ) (hdet τ)
  obtain ⟨y'', t0, hx'', hu'', hs''⟩ := hR T io y0 z hx k hk
  refine ⟨fun o => Option.casesOn o t0 (fun p => Units.mk0 (N p.1 p.2 p.2) (hNd p.1 p.2)), y'', ?_⟩
  unfold FrBor
  refine ⟨hx'', fun τ i => ?_, hs''⟩
  refine ⟨fun j => N τ j i, rfl, fun j hij => hN τ hij, ?_⟩
  obtain ⟨w', hw'⟩ := isCombAt_exists (z.tan τ) (fun j => N τ j i)
  have hw0 : IsCombAt y0.1.x (z.u τ) (fun j => N τ j i) w' := by rw [← hx]; exact hw'
  have hc := hT T.Fr y0.1.x (y0.1.u τ) (y0.1.tan τ) (z.u τ) (A τ) (fun j => N τ j i) w'
    (fun i => ha τ i) hw0
  have hkc : (A τ).mulVec (fun j => N τ j i) = fun j => algebraMap T.V T.Fr (k τ j i) := by
    funext j
    have h3 := congrFun (congrFun (hAN τ) j) i
    rw [Matrix.mul_apply, Matrix.map_apply] at h3
    rw [← h3]
    rfl
  rw [hkc] at hc
  rw [← isCombAt_unique hc (hu'' τ i)]
  exact hw'
end Formalism.L2.PjFree
