-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.lemmaE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:50.866825+00:00
-- url     : https://prove2.me/submissions/bc6cd5dd-72f5-46cd-8734-526e068cc22f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_stepClaim
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_coefficient_L2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_cutBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_gridConvergence
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_leibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_limitA
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_limitB
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_limit_L2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_pairLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem onBoxes_ofFn_of_mem_box (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    (∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ))) → S.OnBoxes (List.ofFn Y) := by
  intro N
  induction N with
  | zero =>
    intro Y _
    rw [List.ofFn_zero]
    exact trivial
  | succ N ih =>
    intro Y hY
    rw [List.ofFn_succ]
    show Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)
    refine ⟨?_, ih _ (fun i => ?_)⟩
    · convert hY 0 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    · convert hY i.succ using 2
      simp only [Fin.val_succ]
      omega
private theorem mem_box_of_onBoxes_ofFn (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) → ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by
  intro N
  induction N with
  | zero =>
    intro Y _ a
    exact a.elim0
  | succ N ih =>
    intro Y hY a
    rw [List.ofFn_succ] at hY
    have hY' : Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧
        S.OnBoxes (List.ofFn fun i => Y i.succ) := hY
    induction a using Fin.cases with
    | zero =>
      convert hY'.1 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    | succ i =>
      convert ih _ hY'.2 i using 2
      simp only [Fin.val_succ]
      omega
private theorem degreeOf_prod_le_sum_degreeOf {σ ι : Type} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    MvPolynomial.degreeOf i (∏ j ∈ s, f j) ≤ ∑ j ∈ s, MvPolynomial.degreeOf i (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, ← MvPolynomial.C_1, MvPolynomial.degreeOf_C]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add_left ih _)
private theorem degreeOf_C_mul_prod_X_add_C_le (N m : ℕ) (c : ℝ) (lam : Fin m → ℝ) (i : Fin N) :
    MvPolynomial.degreeOf i (MvPolynomial.C c *
      ∏ a : Fin N, ∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) ≤ m := by
  classical
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have h1 : ∑ a ∈ Finset.univ.erase i,
      MvPolynomial.degreeOf i (∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    refine Nat.eq_zero_of_le_zero ((degreeOf_prod_le_sum_degreeOf i _ _).trans (le_of_eq (Finset.sum_eq_zero (fun s _ => ?_))))
    refine Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le _ _ _).trans ?_)
    rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_neg (Ne.symm hai)]
    simp
  rw [h1, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  calc ∑ s : Fin m, MvPolynomial.degreeOf i (MvPolynomial.X i + MvPolynomial.C (lam s))
      ≤ ∑ _s : Fin m, 1 := Finset.sum_le_sum (fun s _ => by
        refine (MvPolynomial.degreeOf_add_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_pos rfl]
        simp)
    _ = m := by simp
private theorem le_constants_proof : Formalism.FourierDecayAlt.LE.Constants := by
  intro k r N C₂ C₆ I hN hC₂ hC₆ hI
  have hNr : (r:ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hQ0 : (0:ℝ) ≤ ((r:ℝ) + 1) ^ 2 := by positivity
  have hkNQ : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ) + 1) ^ 2 := by positivity
  have hN2Q : (0:ℝ) ≤ (N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2 := by positivity
  have h26 : C₂ ≤ C₆ := by linarith
  have hC6 : 0 ≤ C₆ := by linarith
  have e1 : C₂ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right h26 hkNQ
  have e2 : (6 * C₂) * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hC₆ hN2Q
  have e3 : ((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2) ≤ (N:ℝ) * (N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hNr (by positivity)
  have e4 : C₂ * (((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2)) ≤ C₂ * ((N:ℝ) * (N * ((r:ℝ) + 1) ^ 2)) :=
    mul_le_mul_of_nonneg_left e3 hC₂.le
  have e5 : 0 ≤ C₂ * ((N:ℝ) * ((r:ℝ) + 1) ^ 2) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · push_cast
    nlinarith
  · nlinarith
private theorem le_constSign_proof : Formalism.FourierDecayAlt.LE.ConstSign := by
  intro n lam α β h
  classical
  by_cases hab : α ≤ β
  · refine ⟨∏ s, (if -lam s < α then (1:ℝ) else -1), ?_, ?_⟩
    · refine Finset.prod_induction _ (fun x : ℝ => x = 1 ∨ x = -1) ?_ ?_ ?_
      · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
      · left; rfl
      · intro s _
        split_ifs <;> simp
    · intro Y hY
      rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun s _ => ?_)
      have hs := h s
      split_ifs with hlt
      · rw [abs_of_pos (by linarith [hY.1])]
        ring
      · have hb : β < -lam s := by
          by_contra hc
          push_neg at hc
          exact hs ⟨not_lt.mp hlt, hc⟩
        rw [abs_of_neg (by linarith [hY.2])]
        ring
  · exact ⟨1, Or.inl rfl, fun Y hY => absurd (le_trans hY.1 hY.2) hab⟩
private theorem le_boxesFit_proof : Formalism.FourierDecayAlt.LE.BoxesFit := by
  intro S hL hfit
  have hL0 : 0 < S.L := by linarith
  have hN0 : (0:ℝ) ≤ S.Ntot := Nat.cast_nonneg _
  have hαβ : S.α ≤ S.β := by nlinarith [mul_nonneg hN0 hL0.le]
  have hmid : ∀ a, a < S.Ntot →
      S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro a ha x hx
    have ha1 : a + 1 ≤ S.Ntot := ha
    have ha' : (a:ℝ) + 1 ≤ S.Ntot := by exact_mod_cast ha1
    have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : 0 ≤ 2 * (a:ℝ) * S.L := by positivity
    have h2 := mul_le_mul_of_nonneg_right ha' hL0.le
    constructor
    · linarith
    · nlinarith
  have hsep : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x := by
    intro a b hab x hx y hy
    have hab1 : a + 1 ≤ b := hab
    have hab' : (a:ℝ) + 1 ≤ b := by exact_mod_cast hab1
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    nlinarith [mul_le_mul_of_nonneg_right hab' hL0.le]
  refine ⟨hmid, hsep, ?_⟩
  have hmem : ∀ w : List ℝ, S.OnBoxes w → ∀ Z ∈ w, ∃ j, j < w.length ∧ Z ∈ S.box j := by
    intro w
    induction w with
    | nil =>
      intro _ Z hZ
      simp at hZ
    | cons Y w ih =>
      intro hOn Z hZ
      have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
      rcases List.mem_cons.mp hZ with rfl | hZ'
      · exact ⟨w.length, by simp only [List.length_cons]; omega, hOn'.1⟩
      · obtain ⟨j, hj, hZj⟩ := ih hOn'.2 Z hZ'
        exact ⟨j, by simp only [List.length_cons]; omega, hZj⟩
  have hin : ∀ j, j < S.Ntot → ∀ x ∈ S.box j, x ∈ Set.Icc S.α S.β := by
    intro j hj x hx
    have hx' := hmid j hj hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨fun x hx => ?_, List.Pairwise.nil⟩
    simp [Formalism.FourierDecayAlt.LE.plus] at hx
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨ih1, ih2⟩ := ih hOn'.2 (by omega)
    show (∀ x ∈ (true, Y) :: Formalism.FourierDecayAlt.LE.plus w, x.2 ∈ Set.Icc S.α S.β) ∧
      ((true, Y) :: Formalism.FourierDecayAlt.LE.plus w).Pairwise fun x y => 2 < |x.2 - y.2|
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hin _ hlen' _ hOn'.1
      · exact ih1 x hx'
    · refine List.Pairwise.cons ?_ ih2
      intro z hz
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hz
      obtain ⟨j, hj, hZj⟩ := hmem w hOn'.2 Z hZ
      have hd := hsep j w.length hj Z hZj Y hOn'.1
      show 2 < |Y - Z|
      rw [abs_of_pos (by linarith)]
      linarith
private theorem le_claimAll_proof : Formalism.FourierDecayAlt.LE.ClaimAll := by
  intro hStep hInd S σ CR Cd CP hσ hCR hCd hCP hL hbig hJL2 hImp
  refine hInd S hJL2 ?_
  intro w Y hOn hlen hint
  have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
  have hY : Y ∈ (S.step w).J := by
    show Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)
    rw [S.step_a, S.step_L]
    exact hOn'.1
  have hst := hStep S.B (S.step w) S.c σ CR Cd CP hσ hCR hCd hCP (by rw [S.step_L]; exact hL)
    (by rw [S.step_r, S.step_L]; exact hbig) (hImp w hOn'.2 hlen) hint Y hY
  have hfun : S.dens (Y :: w) = fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω :=
    funext (S.step_new w Y)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hst.1
  · calc ∫ ω, S.dens (Y :: w) ω ∂S.B.μ
        = ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω ∂S.B.μ := by rw [hfun]
      _ = |(S.step w).P Y| * (S.step w).A0 := hst.2
      _ = |S.P Y| * ∫ ω, S.dens w ω ∂S.B.μ := by
        rw [S.step_P]
        rfl
private theorem le_claimInduction_proof : Formalism.FourierDecayAlt.LE.ClaimInduction := by
  intro S hJL2 hstep w
  induction w with
  | nil =>
    intro _ _
    refine ⟨hJL2, ?_⟩
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_nil, List.prod_nil, one_mul]
    rfl
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨hi, he⟩ := ih hOn'.2 hlen'.le
    have h := hstep w Y hOn hlen' hi
    refine ⟨h.1, ?_⟩
    rw [h.2, he]
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_cons, List.prod_cons]
    ring
private theorem le_eFromConstituents_proof : Formalism.FourierDecayAlt.LE.LemmaEFromSteps := by
  intro hConst hRed hGrid hSign hFit hAll hStep hInd hBL hLB hLA hLL2 hPL hCL2 hLeib hCut
  intro CR Cd CP hCR hCd hCP C₂ hC₂ C₆ hC₆ S hN hL hI hRO hI1 hJL2 hThm hImp hFam
  have hC₂64 : 64 ≤ C₂ :=
    le_trans (le_mul_of_one_le_right (by norm_num) (le_add_of_nonneg_right (by positivity))) hC₂
  have hN1' : 1 ≤ S.Ntot := by omega
  have hN1 : (1:ℝ) ≤ S.Ntot := by exact_mod_cast hN1'
  have hr0 : (0:ℝ) ≤ S.r := Nat.cast_nonneg _
  have hQ : (1:ℝ) ≤ ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ : (1:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ0 : (0:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by linarith
  have hL64 : 64 ≤ S.L := by
    rw [hL]
    nlinarith [mul_le_mul hC₂64 hNQ (by norm_num) (by linarith)]
  have hL2 : 2 < S.L := by linarith
  have hL0 : 0 < S.L := by linarith
  obtain ⟨-, -, h6⟩ := hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hN (by linarith) hC₆ hI
  have hfit : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α := by
    rw [hL]
    linarith
  have hσ : (4:ℝ) ≤ 4 * (S.Ntot:ℝ) := by linarith
  have hclaims := hAll hStep hInd S (4 * (S.Ntot:ℝ)) CR Cd CP hσ hCR hCd hCP hL0
    (by rw [hL]; nlinarith [mul_le_mul_of_nonneg_right hC₂ hNQ0]) hJL2 hImp
  have hBox := hBL hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hclaims
  exact hRed hGrid hSign hFit S hL2 hfit hRO hI1 hBox
private theorem le_reduceToBoxes_proof : Formalism.FourierDecayAlt.LE.ReduceToBoxes := by
  intro hGrid hSign hFit S hL hfit hRO hI1 hBox w hw hlen
  classical
  obtain ⟨sg0, -, hsg⟩ := hSign (S.k + 2 * S.r + 1) S.lam S.α S.β hRO
  obtain ⟨hmid, -, hadm⟩ := hFit S hL hfit
  have hL0 : 0 < S.L := by linarith
  suffices h : ∀ (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ),
      S.admitted (List.ofFn fun a => (sg a, Y a)) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn)) by
    have hwe : (List.ofFn fun a : Fin w.length => ((w.get a).1, (w.get a).2)) = w := by
      simp only [Prod.mk.eta]
      exact List.ofFn_get w
    have h' := h w.length (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [hwe]; exact hw) hlen
    rw [hwe] at h'
    exact h'
  intro N sg Y hadmY hN
  have hex : ∀ ε : ℝ, ∃ Q : MvPolynomial (Fin N) ℝ,
      (∀ a, Q.degreeOf a ≤ S.k + 2 * S.r + 1) ∧
      (0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' Q) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨Q, hQ1, hQ2⟩ := hI1 ε hε N hN
      exact ⟨Q, hQ1, fun _ => hQ2⟩
    · exact ⟨0, fun a => by simp, fun h => absurd h hε⟩
  choose Qf hQf using hex
  set Q₀ : MvPolynomial (Fin N) ℝ := MvPolynomial.C (sg0 ^ N * S.jn) *
    ∏ a : Fin N, ∏ s : Fin (S.k + 2 * S.r + 1), (MvPolynomial.X a + MvPolynomial.C (S.lam s)) with hQ₀
  have hdeg0 : ∀ a, Q₀.degreeOf a ≤ S.k + 2 * S.r + 1 := fun a => degreeOf_C_mul_prod_X_add_C_le _ _ _ _ a
  have hval : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ Set.Icc S.α S.β) → ∀ sg' : Fin N → Bool,
      S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀ := by
    intro Y' hY' sg'
    have habs : ∀ a, |S.P (Y' a)| = sg0 * ∏ s, (Y' a + S.lam s) := fun a => hsg (Y' a) (hY' a)
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
    rw [hQ₀]
    simp only [map_mul, map_prod, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp only [habs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hc : (0:ℝ) < ((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1 := by positivity
  let grid : Fin N → Finset ℝ := fun a => (Finset.range (S.k + 2 * S.r + 1 + 1)).image
    (fun i : ℕ => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L +
      (i : ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)))
  have hcard : ∀ a, (grid a).card = S.k + 2 * S.r + 1 + 1 := by
    intro a
    rw [Finset.card_image_of_injective _ (fun i j hij => by
      have hq : (0:ℝ) < S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1) := div_pos hL0 hc
      have h2 := add_left_cancel hij
      exact_mod_cast mul_right_cancel₀ hq.ne' h2)]
    exact Finset.card_range _
  have hconv : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ grid a) →
      Filter.Tendsto (fun t => MvPolynomial.eval Y' (Qf t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (MvPolynomial.eval Y' Q₀)) := by
    intro Y' hY'
    have hbox : ∀ a : Fin N, Y' a ∈ S.box (N - 1 - (a : ℕ)) := by
      intro a
      obtain ⟨i, hi, hiY⟩ := Finset.mem_image.mp (hY' a)
      rw [← hiY]
      have hi' : (i:ℝ) ≤ ((S.k + 2 * S.r + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      have h0 : 0 ≤ (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) :=
        mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL0.le hc.le)
      have h1 : (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) ≤ S.L := by
        rw [mul_div_assoc', div_le_iff₀ hc]
        nlinarith [mul_le_mul_of_nonneg_right hi' hL0.le]
      constructor
      · linarith
      · linarith
    have hOnY : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' hbox
    have hb := hBox (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    have hplus : Formalism.FourierDecayAlt.LE.plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a) := by
      simp only [Formalism.FourierDecayAlt.LE.plus, List.map_ofFn]
      rfl
    have hIcc : ∀ a, Y' a ∈ Set.Icc S.α S.β := fun a => by
      have ha := a.isLt
      have hm := hmid (N - 1 - (a : ℕ)) (by omega) (hbox a)
      have hαβ : S.α ≤ S.β := by linarith [hm.1, hm.2]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
    rw [hplus, hval Y' hIcc (fun _ => true)] at hb
    refine hb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hA := hadm (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    rw [hplus] at hA
    exact (hQf ε).2 hε (fun _ => true) Y' hA
  have hlim := hGrid N (S.k + 2 * S.r + 1) ℝ (nhdsWithin 0 (Set.Ioi 0)) Qf Q₀ grid
    (fun t a => (hQf t).1 a) hdeg0 hcard hconv Y
  obtain ⟨hA1, -⟩ := id hadmY
  have hIcc : ∀ a, Y a ∈ Set.Icc S.α S.β := fun a =>
    hA1 (sg a, Y a) (by simp only [List.mem_ofFn]; exact ⟨a, rfl⟩)
  rw [hval Y hIcc sg]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ((hQf ε).2 hε sg Y hadmY).symm
private theorem le_boxLimitFromClaim_proof : Formalism.FourierDecayAlt.LE.BoxLimitFromClaim := by
  intro hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hClaim w hw hlen
  suffices h : ∀ (N : ℕ) (Y : Fin N → ℝ), S.OnBoxes (List.ofFn Y) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn)) by
    have h' := h w.length w.get (by rw [List.ofFn_get]; exact hw) hlen
    rw [List.ofFn_get] at h'
    exact h'
  intro N Y hOn hN
  have hInt : ∀ Y' : Fin N → ℝ, (S.fam N).On Y' →
      MeasureTheory.Integrable
        (Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ := by
    intro Y' hY'
    have hOn' : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' (fun a => by
      have h := hY' a
      rw [S.fam_J] at h
      exact h)
    have hc := (hClaim (List.ofFn Y') hOn' (by rw [List.length_ofFn]; exact hN)).1
    have hfun : S.dens (List.ofFn Y') =
        fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) ω :=
      funext (S.fam_dens N Y')
    rw [hfun] at hc
    exact hc
  have hJinf : ∀ a, ((S.fam N).J a).Infinite := by
    intro a
    rw [S.fam_J]
    exact Set.Icc_infinite (by linarith)
  have hOnF : ∀ a, Y a ∈ (S.fam N).J a := by
    intro a
    have h := mem_box_of_onBoxes_ofFn S N Y hOn a
    rw [S.fam_J]
    exact h
  have hlim := hLB hLA hLL2 hPL hCL2 hLeib hCut S.B N (S.fam N) S.c hJinf (hFam N hN) hInt Y hOnF
  have hval : S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn =
      ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y) ((S.fam N).gw Y (S.fam N).u) ω ∂S.B.μ := by
    rw [← (hClaim (List.ofFn Y) hOn (by rw [List.length_ofFn]; exact hN)).2]
    exact congrArg (MeasureTheory.integral S.B.μ) (funext fun ω => S.fam_dens N Y ω)
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hThm N Y hN hOn ε hε).symm
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (hC : E.CauchyTheta) (hMV : E.MarkovVector) : LemmaE :=
  le_eFromConstituents_proof le_constants_proof le_reduceToBoxes_proof gridConvergence le_constSign_proof le_boxesFit_proof
    le_claimAll_proof (stepClaim hC hMV) le_claimInduction_proof le_boxLimitFromClaim_proof limitB limitA limit_L2
    pairLimit coefficient_L2 leibniz cutBound
end Formalism.FourierDecayAlt.P.LEx2
