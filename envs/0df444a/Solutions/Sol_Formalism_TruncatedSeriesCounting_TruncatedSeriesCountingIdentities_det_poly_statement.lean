-- Prove2me | solution 1 for Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.det_poly_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:29.632433+00:00
-- url     : https://prove2.me/submissions/0a952e62-1fcd-4340-bdbf-3fa7b12e70ae

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_core
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_mem_mainNotions_iff_fromT
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_charpolyRev_map
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_det_eq_coeff
import Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_F_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
open DetPolyCore DetPolyApp
namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
theorem _root_.solution : LemmaDetPoly := by
  intro O K Xs G _ _ _ _ n _ _ T r hchar m a ha s
  choose sg c hc hae using ha
  let coefL : (Σ _ : Fin m, G) → Xs → MvPolynomial (Fin m) K :=
    fun p x => MvPolynomial.X p.1 * MvPolynomial.C (algebraMap O K (c p.1 p.2 x))
  have hcoef : ∀ p, coefL p ∈ S1 (K := K) T m := by
    intro p α
    show FromT T (fun x => (MvPolynomial.X p.1 * MvPolynomial.C (algebraMap O K (c p.1 p.2 x))).coeff α)
    simp only [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_C]
    by_cases h1 : p.1 ∈ α.support
    · by_cases h2 : (0 : Fin m →₀ ℕ) = α - Finsupp.single p.1 1
      · simp only [h1, h2, if_true]
        exact ⟨c p.1 p.2, hc p.1 p.2, fun x => rfl⟩
      · simp only [h1, h2, if_true, if_false]
        exact mem_mainNotions_iff_fromT.1 (MainNotions (K := K) T).zero_mem
    · simp only [h1, if_false]
      exact mem_mainNotions_iff_fromT.1 (MainNotions (K := K) T).zero_mem
  have hS : ∀ g k, (Matrix.charpolyRev (rho r m g)).coeff k ∈ S1 (K := K) T m := by
    intro g k α
    have e : ∀ x, (Matrix.charpolyRev (rho r m g)).coeff k x =
        MvPolynomial.C ((Matrix.charpolyRev (r g x)).coeff k) := by
      intro x
      have h1 : (Matrix.charpolyRev (rho r m g)).coeff k x =
          ((Matrix.charpolyRev (rho r m g)).map
            (Pi.evalRingHom (fun _ : Xs => MvPolynomial (Fin m) K) x)).coeff k := by
        rw [Polynomial.coeff_map]; rfl
      rw [h1, charpolyRev_map,
        show (rho r m g).map (Pi.evalRingHom (fun _ : Xs => MvPolynomial (Fin m) K) x) =
          (r g x).map MvPolynomial.C from Matrix.ext fun i j => rfl,
        ← charpolyRev_map, Polynomial.coeff_map]
    show FromT T (fun x => ((Matrix.charpolyRev (rho r m g)).coeff k x).coeff α)
    simp only [e, MvPolynomial.coeff_C]
    by_cases h : (0 : Fin m →₀ ℕ) = α
    · simp only [h, if_true]; exact hchar g k
    · simp only [h, if_false]; exact mem_mainNotions_iff_fromT.1 (MainNotions (K := K) T).zero_mem
  set l : List ((Xs → MvPolynomial (Fin m) K) × ℕ × G) :=
    ((Finset.univ : Finset (Fin m)).sigma sg).toList.map (fun p => (coefL p, 1, p.2)) with hl_def
  have hl : ∀ L ∈ l, L.1 ∈ S1 (K := K) T m ∧ 1 ≤ L.2.1 := by
    intro L hL
    rw [hl_def] at hL
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hL
    exact ⟨hcoef p, le_rfl⟩
  have hl1 : ∀ L ∈ l, L.2.1 = 1 := by
    intro L hL
    rw [hl_def] at hL
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hL
    rfl
  set Mt := (l.map (fun L => L.1 • rho r m L.2.2)).sum with hMt
  have hcore := core (rho r m) hS l hl (Fintype.card n)
  have hF : F (rho r m) l = Matrix.charpolyRev Mt := by
    unfold F Matrix.charpolyRev
    rw [F_eq _ l hl1]
  rw [hF] at hcore
  have hdet : Mt.det ∈ S1 (K := K) T m := by
    rw [det_eq_coeff]
    exact (S1 (K := K) T m).mul_mem ((S1 (K := K) T m).pow_mem
      ((S1 (K := K) T m).neg_mem (S1 (K := K) T m).one_mem) _) hcore
  have hx : ∀ x, Mt.det x = Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) K) •
      (a i x).map MvPolynomial.C) := by
    intro x
    rw [show Mt.det x = Pi.evalRingHom (fun _ : Xs => MvPolynomial (Fin m) K) x Mt.det from rfl,
      RingHom.map_det]
    congr 1
    rw [hMt, hl_def, map_list_sum, List.map_map, List.map_map, Finset.sum_map_toList,
      Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hae i]
    refine Matrix.ext fun i' j' => ?_
    simp [coefL, rho, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum, mul_assoc]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Algebra.smul_def, map_mul]
  obtain ⟨t, ht, htx⟩ := hdet s
  exact ⟨t, ht, fun x => by rw [htx x]; exact congrArg (MvPolynomial.coeff s) (hx x)⟩
end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
