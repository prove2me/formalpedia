-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_ReduceToBoxes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:34:17.489714+00:00
-- url     : https://prove2.me/submissions/6cf98392-13f1-4440-9ceb-d12551c5e02f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_onBoxes_ofFn
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_degreeOf_prod_linear_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_size_ofFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : ReduceToBoxes := by
  classical
  intro hGrid hSign hFit S hL h6 hRoots hI1 hBox w hA hlen
  obtain ⟨sgn, _, hsgn⟩ := hSign _ S.lam S.α S.β hRoots
  obtain ⟨hsub, _, hAdm⟩ := hFit S hL h6
  have key : ∀ (N : ℕ), N ≤ S.Ntot → ∀ (sg : Fin N → Bool) (Y : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg a, Y a)) →
      Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (𝓝[>] 0)
        (𝓝 (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn)) := by
    intro N hN sg Y hAY
    let Q : ℝ → MvPolynomial (Fin N) ℝ := fun ε => if h : 0 < ε then (hI1 ε h N hN).choose else 0
    let Q₀ : MvPolynomial (Fin N) ℝ :=
      MvPolynomial.C (sgn ^ N * S.jn) * ∏ b : Fin N, ∏ s, (MvPolynomial.X b + MvPolynomial.C (S.lam s))
    have hQ : ∀ ε, 0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' (Q ε) := by
      intro ε hε sg' Y' h'
      simp only [Q, dif_pos hε]
      exact (hI1 ε hε N hN).choose_spec.2 sg' Y' h'
    have hQd : ∀ ε a, (Q ε).degreeOf a ≤ S.k + 2 * S.r + 1 := by
      intro ε a
      by_cases hε : 0 < ε
      · simp only [Q, dif_pos hε]; exact (hI1 ε hε N hN).choose_spec.1 a
      · simp [Q, dif_neg hε]
    have hQ0 : ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀ := by
      intro sg' Y' h'
      rw [size_ofFn]
      have : ∀ a, |S.P (Y' a)| = sgn * S.P (Y' a) := by
        intro a
        apply hsgn
        exact h'.1 (sg' a, Y' a) (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
      rw [Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      simp only [Q₀, map_mul, MvPolynomial.eval_C, map_prod, map_add, MvPolynomial.eval_X, Sys.P]
      ring
    let n := S.k + 2 * S.r + 1
    let lo : Fin N → ℝ := fun a => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L
    let grid : Fin N → Finset ℝ := fun a => (Finset.range (n + 1)).image fun i : ℕ => lo a + S.L * ((i : ℝ) / (n + 1))
    have hcard : ∀ a, (grid a).card = n + 1 := by
      intro a
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro i i' h
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hL0 : S.L ≠ 0 := by linarith
      have h1 : S.L * ((i : ℝ) / (n + 1)) = S.L * ((i' : ℝ) / (n + 1)) := by simpa using h
      have h2 := mul_left_cancel₀ hL0 h1
      have h3 : (i : ℝ) = i' := by field_simp at h2; exact h2
      exact_mod_cast h3
    have hgm : ∀ a, ∀ y ∈ grid a, y ∈ S.box (N - 1 - (a : ℕ)) := by
      intro a y hy
      simp only [grid, Finset.mem_image, Finset.mem_range] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hi
      have h01 : (i : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h00 : (0:ℝ) ≤ (i : ℝ) / (n + 1) := by positivity
      constructor
      · show lo a ≤ _
        nlinarith
      · show _ ≤ lo a + S.L
        nlinarith
    have hconv := hGrid N n ℝ (𝓝[>] 0) Q Q₀ grid hQd (fun a => degreeOf_prod_linear_le N _ S.lam _ a) hcard (by
      intro Y' hY'
      have hOn : S.OnBoxes (List.ofFn Y') := (onBoxes_ofFn S N Y').mpr fun a => hgm a _ (hY' a)
      have hlen' : (List.ofFn Y').length ≤ S.Ntot := by rw [List.length_ofFn]; exact hN
      have hb := hBox _ hOn hlen'
      have hAd := hAdm _ hOn hlen'
      have e : plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a) := by
        unfold plus; rw [List.map_ofFn]; rfl
      rw [e] at hb hAd
      rw [hQ0 _ _ hAd] at hb
      refine hb.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hQ ε hε _ _ hAd) Y
    rw [hQ0 _ _ hAY]
    refine hconv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hQ ε hε _ _ hAY).symm
  have e : (List.ofFn fun a => ((w.get a).1, (w.get a).2)) = w := by
    have : (fun a => ((w.get a).1, (w.get a).2)) = w.get := by funext a; rfl
    rw [this, List.ofFn_get]
  have := key w.length hlen (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [e]; exact hA)
  rwa [e] at this
end Formalism.FourierDecayAlt.P.LEx2
