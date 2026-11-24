-- Prove2me | solution 1 for Formalism.GM.TM.theoremM_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:38.432988+00:00
-- url     : https://prove2.me/submissions/0b2e2877-0beb-47c5-b8f5-a53f42721858

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_takeD_setTies_update
import Theorems.Thm_Formalism_GM_TM_setTies_deg_eta
import Theorems.Thm_Formalism_GM_TM_setTies_deg_mono
import Theorems.Thm_Formalism_GM_TM_takeD_total_eq
import Theorems.Thm_Formalism_GM_TM_S_mono
import Theorems.Thm_Formalism_GM_TM_finrank_of_lattice_basis
import Theorems.Thm_Formalism_GM_TM_mmw_ne_bot_box
import Theorems.Thm_Formalism_GM_TM_smith_qp
import Theorems.Thm_Formalism_GM_TM_grid_average
import Theorems.Thm_Formalism_GM_TM_lg_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
namespace Formalism.GM.TM
theorem _root_.solution (hMean : MeanGam) (hMono : WeightSpaceDimMonotone) (hCount : MonoCount) (hSmith : SmithZp)
    (hAd : AdaptedBasisExists) (hPt : PointM) : TheoremM := by
  obtain ⟨C₀', hC₀', hMG⟩ := hMean
  obtain ⟨C₁, hC₁, hPW⟩ := hPt
  refine ⟨max C₀' C₁, le_trans hC₁ (le_max_right _ _), ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp2 hr hρ hadm hE hYd hS hdeg hz hκ hHyp
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg : 0 ≤ lgV2 p a r := lg_nonneg p a r hr
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ

  choose nb fb ord hli hsp hord hfil using fun (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) =>
    hAd p (T.pos i) r L0 T.J (T.thrUpTo i) ρ w
  choose Uc Vc dgc hUc using fun (k : ℕ) (A : Matrix (Fin k) (Fin k) ℚ_[p]) => smith_qp hSmith A
  have hfwex : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ), ∃ g,
      g ∈ MMw p L0 T.J (T.thrUpTo i) ρ w ∧ (MMw p L0 T.J (T.thrUpTo i) ρ w ≠ ⊥ → g ≠ 0) := by
    intro i L0 w
    by_cases h : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
    · exact ⟨0, Submodule.zero_mem _, fun h' => absurd h h'⟩
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      exact ⟨g, hg, fun _ => hg0⟩
  choose fw hfw using hfwex
  have hnb : ∀ i L0 w, nb i L0 w = Module.finrank ℚ_[p] (MMw p L0 T.J (T.thrUpTo i) ρ w) := fun i L0 w =>
    (finrank_of_lattice_basis _ (fb i L0 w) (hli i L0 w) (hsp i L0 w)).symm
  let MatF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ),
      Matrix (Fin (nb i L0 w)) (Fin (nb i L0 w)) ℚ_[p] := fun i L0 w y =>
    Matrix.of fun x x' => (p : ℚ_[p]) ^ (⌈κ⌉₊) * tieGam p L0 ρ (T.z i) y (fb i L0 w x) (fb i L0 w x')
  let cntF : ∀ (i : Fin T.t) (L0 : Letters (T.pos i + 1)) (w : Fin r → ℤ) (y : ℕ), ℕ := fun i L0 w y =>
    (univ.filter (fun b => ‖dgc _ (MatF i L0 w y) b‖ < (p : ℝ) ^ (-E))).card
  let Bx : ∀ i : Fin T.t, Letters (T.pos i + 1) → Finset (Fin r → ℤ) := fun i L0 =>
    Fintype.piFinset fun _ => Icc (-(L0.total : ℤ)) L0.total
  have hcntle : ∀ i L0 w y, cntF i L0 w y ≤ nb i L0 w := fun i L0 w y =>
    (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hbot : ∀ i L0 w, w ∉ Bx i L0 → MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥ := fun i L0 w hw => by
    by_contra h; exact hw (mmw_ne_bot_box L0 T.J (T.thrUpTo i) ρ w h)
  have hnb0 : ∀ i L0 w, w ∉ Bx i L0 → nb i L0 w = 0 := fun i L0 w hw => by
    rw [hnb, hbot i L0 w hw, finrank_bot]
  have hcnt0 : ∀ i L0 w y, w ∉ Bx i L0 → cntF i L0 w y = 0 := fun i L0 w y hw =>
    Nat.eq_zero_of_le_zero ((hcntle i L0 w y).trans (hnb0 i L0 w hw).le)
  let sI : Fin T.t → Finset ℕ := fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)
  let top : Fin T.t → ℕ := fun i => n₀ i + dd i * (Yl i - 1)
  have hsI : ∀ i y, y ∈ sI i → n₀ i ≤ y ∧ y ≤ top i := by
    intro i y hy
    simp only [sI, mem_image, mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _⟩
  have hgrid : ∀ n ∈ Fintype.piFinset sI, ∀ i, n₀ i ≤ n i ∧ n i ≤ top i := fun n hn i =>
    hsI i (n i) (Fintype.mem_piFinset.mp hn i)
  have hinj : ∀ i, Set.InjOn (fun j => n₀ i + dd i * j) (range (Yl i) : Set ℕ) := by
    intro i x _ y _ hxy
    have := (hYd i).2.1
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_left this (by omega)
  have hcard : ∀ i, (sI i).card = Yl i := fun i => by
    simp only [sI]; rw [Finset.card_image_of_injOn (hinj i), Finset.card_range]
  let BB : Fin T.t → (Fin T.t → ℕ) → ℝ := fun i n =>
    ∑ w ∈ Bx i ((LL.setTies T n).takeD (T.pos i + 1)),
      (cntF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)) : ℝ)
  refine grid_average sI (fun n => (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
      (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + max C₀' C₁ * κ) + max C₀' C₁ * κ⌋ : ℝ)) BB
    (fun i n => (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ))
    (fun i => 2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
      (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E)
    (fun i => by rw [hcard]; exact (hYd i).1) ?_ ?_
  · intro n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    have hSn : ∀ i, T.S (LL.setTies T n) i ≤ n i := fun i =>
      (S_mono LL T n top hnt i).trans ((hS i).trans (hgrid n hn i).1)
    have hdegn : ∀ x, (LL.setTies T n).deg x ≤ 2 * a := fun x =>
      (setTies_deg_mono LL T n top hnt x).trans (hdeg x)
    obtain ⟨hP, hW, hL4⟩ := hHyp n hn
    have key := hPW (max C₀' C₁) (le_max_right _ _) p N r LL T a E κ n ρ hp2 hr hρ hadm hE hSn hdegn hz hκ hP hW hL4
      (fun i w => nb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => fb i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => Uc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => Vc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => dgc _ (MatF i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i)))
      (fun i w => fw i ((LL.setTies T n).takeD (T.pos i + 1)) w)
      (fun i w => ⟨hli _ _ _, hsp _ _ _⟩) (fun i w => hUc _ _) (fun i w => hfw _ _ _)
    refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    apply finsum_eq_sum_of_support_subset
    intro w hw
    by_contra hwn
    apply hw
    have h0 := hcnt0 i ((LL.setTies T n).takeD (T.pos i + 1)) w (n i) hwn
    simp only [cntF] at h0
    simp only [h0, Nat.cast_zero, zero_mul]
  · intro i n hn
    have hnt : ∀ i, n i ≤ top i := fun i => (hgrid n hn i).2
    obtain ⟨hlt, hvW, _⟩ := hadm.2.1 i
    obtain ⟨_, _, hL4⟩ := hHyp n hn
    have hLW : ∀ y, (LL.setTies T (Function.update n i y)).takeD (T.pos i + 1) =
        (LL.setTies T n).takeD (T.pos i + 1) := fun y => takeD_setTies_update LL T n i y
    have hL0S : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ T.S (LL.setTies T top) i := by
      rw [takeD_total_eq (LL.setTies T n) T i hlt]; exact S_mono LL T n top hnt i
    have hL0tot : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n₀ i := hL0S.trans (hS i)
    have hvec : ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by
      simp only [Letters.takeD, Fin.val_last]
      rw [dif_pos (by omega)]
      exact hvW
    have hL0deg : ∀ x, ((LL.setTies T n).takeD (T.pos i + 1)).deg x ≤ 2 * a := by
      intro x
      simp only [Letters.takeD]
      split_ifs
      · exact (setTies_deg_mono LL T n top hnt _).trans (hdeg _)
      · exact Nat.zero_le _
    have hsd : n₀ i + dd i * (Yl i - 1) ≤ 2 * a := by
      have := hdeg ⟨T.pos i + 1, hlt⟩
      rwa [setTies_deg_eta LL T hadm.1 top i hlt] at this
    have hκi : (((T.pos i : ℕ) + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ := by
      refine le_trans ?_ hκ
      have : ((T.pos i : ℕ) + 3 : ℝ) ≤ (N : ℝ) + 2 := by
        have : T.pos i + 3 ≤ N + 2 := by omega
        exact_mod_cast this
      gcongr
    set L0 := (LL.setTies T n).takeD (T.pos i + 1) with hL0
    have e1 : ∀ y, BB i (Function.update n i y) = ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) := by
      intro y
      simp only [BB]
      rw [hLW y, Function.update_self]
    simp only [e1]

    have hmono : ∀ y ∈ sI i, ∀ w, (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ) ≤
        (cntF i L0 w y : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
      intro y hy w
      by_cases hM : MMw p L0 T.J (T.thrUpTo i) ρ w = ⊥
      · have : cntF i L0 w y = 0 := Nat.eq_zero_of_le_zero
          ((hcntle i L0 w y).trans (by rw [hnb, hM, finrank_bot]))
        simp [this]
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hm := hMono p N r LL T hadm ρ hρ hr i (Function.update n i y) w (fw i L0 w)
          (by rw [hLW y]; exact (hfw i L0 w).1) ((hfw i L0 w).2 hM)
          (by rw [hLW y, Function.update_self]; exact hL0tot.trans (hsI i y hy).1) (top i)
          (by rw [Function.update_self]; exact (hsI i y hy).2)
        rw [Function.update_idem] at hm
        exact_mod_cast hm

    have hmean : ∀ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) ≤
        (Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E)) := by
      intro w _
      have hm := hMG p (T.pos i) r L0 T.J (T.thrUpTo i) ρ (T.z i) w (nb i L0 w) (fb i L0 w) (ord i L0 w)
        (n₀ i) (dd i) (Yl i) a E κ (fun j => Uc _ (MatF i L0 w (n₀ i + dd i * j)))
        (fun j => Vc _ (MatF i L0 w (n₀ i + dd i * j))) (fun j => dgc _ (MatF i L0 w (n₀ i + dd i * j)))
        hρ hr hvec (hli _ _ _) (hsp _ _ _) (hord _ _ _) (hfil _ _ _) hE (hYd i).1 (hYd i).2.1 (hYd i).2.2
        hL0tot hL0deg hsd (hz i) hκi (hL4 i) (fun j _ => hUc _ _)
      have hY0 : (0 : ℝ) < Yl i := by exact_mod_cast (hYd i).1
      rw [div_le_iff₀ hY0] at hm
      have hsum : (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) =
          ∑ j ∈ range (Yl i), ((univ.filter (fun b =>
            ‖dgc _ (MatF i L0 w (n₀ i + dd i * j)) b‖ < (p : ℝ) ^ (-E))).card : ℝ) := by
        simp only [sI]
        rw [Finset.sum_image (hinj i)]
      rw [hsum]
      refine hm.trans ?_
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ hY0.le
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hE0 : (0 : ℝ) < E := by linarith
      have hL : ((L0.total : ℕ) : ℝ) ≤ (T.S (LL.setTies T top) i : ℝ) := by exact_mod_cast hL0S
      have hC : C₀' * κ ≤ max C₀' C₁ * κ := mul_le_mul_of_nonneg_right (le_max_left _ _) hκ0
      gcongr

    have hcount : (∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
        (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) =
        (Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T (Function.update n i (top i))) T.J T.thr) : ℝ) := by
      have hc := hCount p N r LL T hadm ρ hρ hr i (Function.update n i (top i))
        (by rw [hLW, Function.update_self]; exact hL0tot.trans (Nat.le_add_right _ _)) (fun w => fw i L0 w)
        (fun w => by rw [hLW]; exact hfw i L0 w)
      rw [hLW] at hc
      rw [finsum_eq_sum_of_support_subset _ (s := Bx i L0) (fun w hw => by
        by_contra hwn
        apply hw
        beta_reduce
        rw [← hnb, hnb0 i L0 w hwn, zero_mul])] at hc
      rw [← hc]
      push_cast
      apply Finset.sum_congr rfl
      intro w _
      rw [hnb]
    calc ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i y) (fw i L0 w)) : ℝ)
        ≤ ∑ y ∈ sI i, ∑ w ∈ Bx i L0, (cntF i L0 w y : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun w _ => hmono y hy w
      _ = ∑ w ∈ Bx i L0, (∑ y ∈ sI i, (cntF i L0 w y : ℝ)) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ ≤ ∑ w ∈ Bx i L0, ((Yl i : ℝ) * ((nb i L0 w : ℝ) * (2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E))) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_right (hmean w hw) (Nat.cast_nonneg _)
      _ = (sI i).card * ((2 * (T.S (LL.setTies T top) i : ℝ) / Yl i +
          (max C₀' C₁ * κ + 2 * (T.S (LL.setTies T top) i : ℝ) * lgV2 p a r / Yl i) / E) *
            ∑ w ∈ Bx i L0, (nb i L0 w : ℝ) *
              (Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i (top i)) (fw i L0 w)) : ℝ)) := by
          rw [hcard, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
      _ = _ := by rw [hcount]
end Formalism.GM.TM
