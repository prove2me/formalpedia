-- Prove2me | solution 1 for DetANN.HPIM.lookupTree_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T06:37:34.911613+00:00
-- url     : https://prove2.me/submissions/f2db5583-ecf3-4a2a-9355-c1a9a97d9bb5

import Mathlib
import Definitions.Def_DetANN_HPIMTree
import Theorems.Thm_DetANN_HPIM_build_struct
import Theorems.Thm_DetANN_HPIM_build_size
import Theorems.Thm_DetANN_HPIM_balance_spec

/-!
# The lookup contract, from `build_struct`, `build_size` and `balance_spec`

M1 (leaf certificates are sound) is proved here.
-/

namespace DetANN.HPIM

variable {m : ℕ}

/-! ## M1: leaf certificates -/

lemma norm_sub_sq_eq_sum (x y : EuclideanSpace ℝ (Fin m)) :
    ‖x - y‖ ^ 2 = ∑ j, (x j - y j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [sq_abs]

lemma sum_sq_le_boxMaxDist2 {lo hi p q : Fin m → ℝ} (hq : InBox lo hi q) :
    ∑ j, (q j - p j) ^ 2 ≤ boxMaxDist2 lo hi p := by
  unfold boxMaxDist2
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨h1, h2⟩ := hq j
  have : |q j - p j| ≤ max (p j - lo j) (hi j - p j) := by
    rw [abs_le]; constructor
    · have := le_max_left (p j - lo j) (hi j - p j); linarith
    · have := le_max_right (p j - lo j) (hi j - p j); linarith
  calc (q j - p j) ^ 2 = |q j - p j| ^ 2 := (sq_abs _).symm
    _ ≤ _ := by gcongr

lemma boxDist2_le_sum_sq {lo hi p q : Fin m → ℝ} (hq : InBox lo hi q) :
    boxDist2 lo hi p ≤ ∑ j, (q j - p j) ^ 2 := by
  unfold boxDist2
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨h1, h2⟩ := hq j
  have h0 : 0 ≤ max (lo j - p j) (max 0 (p j - hi j)) := le_max_of_le_right (le_max_left _ _)
  have : max (lo j - p j) (max 0 (p j - hi j)) ≤ |q j - p j| := by
    refine max_le ?_ (max_le (abs_nonneg _) ?_)
    · exact le_trans (by linarith) (le_abs_self _)
    · rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
  calc (max (lo j - p j) (max 0 (p j - hi j))) ^ 2 ≤ |q j - p j| ^ 2 := by gcongr
    _ = (q j - p j) ^ 2 := sq_abs _

/-- **M1 (IN).** A query in an `IN(p)` box is within `c r` of `p`. -/
lemma certificate_in {lo hi : Fin m → ℝ} {p q : EuclideanSpace ℝ (Fin m)} {cr : ℝ} (hcr : 0 ≤ cr)
    (hq : InBox lo hi q) (hc : boxMaxDist2 lo hi p ≤ cr ^ 2) : ‖q - p‖ ≤ cr := by
  have := (norm_sub_sq_eq_sum q p).trans_le ((sum_sq_le_boxMaxDist2 hq).trans hc)
  exact (sq_le_sq₀ (norm_nonneg _) hcr).1 this

/-- **M1 (OUT).** A query in an `OUT` box is farther than `r` from every point. -/
lemma certificate_out {lo hi : Fin m → ℝ} {p q : EuclideanSpace ℝ (Fin m)} {r : ℝ} (hr : 0 ≤ r)
    (hq : InBox lo hi q) (hc : r ^ 2 < boxDist2 lo hi p) : r < ‖q - p‖ := by
  have := hc.trans_le ((boxDist2_le_sum_sq hq).trans (norm_sub_sq_eq_sum q p).ge)
  exact (sq_lt_sq₀ hr (norm_nonneg _)).1 this

namespace BSP

lemma certified_sub {n : ℕ} {pts : Fin n → Fin m → ℝ} {r c : ℝ} :
    ∀ (T : BSP m) (p : List Bool) {lo hi : Fin m → ℝ} {a : Option ℕ}, T.Certified pts r c →
      T.sub p = some (.leaf lo hi a) → (BSP.leaf lo hi a).Certified pts r c
  | .leaf lo hi a, [], _, _, _, hT, h => by
    simp only [sub, Option.some.injEq, BSP.leaf.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact hT
  | .leaf .., _ :: _, _, _, _, _, h => by simp [sub] at h
  | .cut _ _ _ _, [], _, _, _, _, h => by simp [sub] at h
  | .cut _ _ l _, false :: p, _, _, _, hT, h => certified_sub l p hT.1 h
  | .cut _ _ _ t, true :: p, _, _, _, hT, h => certified_sub t p hT.2 h

end BSP

lemma lookupTree_eq {n : ℕ} (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r c δ : ℝ) :
    lookupTree pts r c δ =
      .test (rootLo hn pts r) (rootHi hn pts r)
        (balance (build pts r c (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r))
          ((build pts r c (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)).paths.card + 1)
          [] ∅) (.leaf none) := by
  unfold lookupTree
  rw [dif_pos hn]

/-- M2: the certified BSP from the root box is certified, covers, has the root box, and is small. -/
theorem build_spec' (hm : 1 ≤ m) {n : ℕ} (hn : 0 < n) (pts : Fin n → Fin m → ℝ) (r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    let T := build pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r) (rootHi hn pts r)
    T.Certified pts r (1 + δ / 4) ∧ T.Covers ∧ T.box = (rootLo hn pts r, rootHi hn pts r) ∧
      T.paths.card ≤ 2 * bspFuel n m δ := by
  obtain ⟨h1, h2⟩ := build_size hm hn pts r δ hr hδ hδ'
  obtain ⟨b, c, d⟩ := build_struct pts r (1 + δ / 4) (bspFuel n m δ) (rootLo hn pts r)
    (rootHi hn pts r)
  exact ⟨d h1, c, b, h2⟩

lemma abs_apply_le_norm (x : EuclideanSpace ℝ (Fin m)) (j : Fin m) : |x j| ≤ ‖x‖ := by
  have h : (x j) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [show x = x - 0 by simp, norm_sub_sq_eq_sum]
    simpa using Finset.single_le_sum (f := fun i => (x i - (0 : EuclideanSpace ℝ (Fin m)) i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  exact abs_le_of_sq_le_sq' h (norm_nonneg _) |> fun h' => abs_le.2 h'

/-- Outside the root box every point is farther than `r`. -/
lemma far_of_not_inBox {n : ℕ} (hn : 0 < n) (P : Fin n → EuclideanSpace ℝ (Fin m)) (r : ℝ)
    (hr : 0 < r) (hm : 1 ≤ m) (q : EuclideanSpace ℝ (Fin m))
    (hq : ¬ InBox (rootLo hn (fun i j => P i j) r) (rootHi hn (fun i j => P i j) r) q)
    (i : Fin n) : r < ‖q - P i‖ := by
  set lo0 : Fin m → ℝ := fun j => Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => P i j)
  set hi0 : Fin m → ℝ := fun j => Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => P i j)
  have hD : 0 ≤ sigma lo0 hi0 := by
    unfold sigma
    have j0 : Fin m := ⟨0, hm⟩
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove j0)
    have := Finset.inf'_le (fun i => P i j0) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    have := Finset.le_sup' (fun i => P i j0) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    simp only [lo0, hi0]; linarith
  unfold InBox at hq
  push Not at hq
  obtain ⟨j, hj⟩ := hq
  have hle := abs_apply_le_norm (q - P i) j
  have hlo : lo0 j ≤ P i j := Finset.inf'_le (fun i => P i j) (Finset.mem_univ i)
  have hhi : P i j ≤ hi0 j := Finset.le_sup' (fun i => P i j) (Finset.mem_univ i)
  have hcoord : (q - P i) j = q j - P i j := rfl
  rw [hcoord] at hle
  by_cases h1 : rootLo hn (fun i j => P i j) r j ≤ q j
  · have h2 := hj h1
    simp only [rootHi] at h2
    have : r < |q j - P i j| := lt_of_lt_of_le (by linarith) (le_abs_self _)
    linarith
  · push Not at h1
    simp only [rootLo] at h1
    have : r < |q j - P i j| := by
      rw [abs_sub_comm]; exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    linarith

/-- **M123.** One lookup structure satisfies the NearNbr contract, with a logarithmic visit count
(from M1, M2, M3). -/
theorem lookupTree_spec_aux (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) (P : Fin n → EuclideanSpace ℝ (Fin m))
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    NearNbrSpec P r (1 + δ / 4) (lookupTree (fun i j => P i j) r (1 + δ / 4) δ) ∧
    ∀ q : Fin m → ℝ, (lookupTree (fun i j => P i j) r (1 + δ / 4) δ).visits q ≤
      5 * Nat.log 2 (2 * bspFuel n m δ) + 7 := by
  have hn0 : 0 < n := hn
  obtain ⟨hcert, hcov, hbox, hsize⟩ := build_spec' hm hn0 (fun i j => P i j) r δ hr hδ hδ'
  set T := build (fun i j => P i j) r (1 + δ / 4) (bspFuel n m δ)
    (rootLo hn0 (fun i j => P i j) r) (rootHi hn0 (fun i j => P i j) r) with hT
  have hc : 0 ≤ (1 + δ / 4) * r := by positivity
  rw [lookupTree_eq hn0]
  refine ⟨fun q => ⟨fun i hi => ?_, fun hnone j => ?_⟩, fun q => ?_⟩
  · -- an answer comes from a certified IN leaf containing q
    simp only [BoxTree.eval] at hi
    split_ifs at hi with hq
    · have hq' : InBox T.box.1 T.box.2 q := by rw [hbox]; exact hq
      obtain ⟨p, lo, hi', a, hsub, hin, heval⟩ := (balance_spec T hcov q).1 hq'
      rw [← hT, heval] at hi
      subst hi
      obtain ⟨hlt, hcer⟩ := BSP.certified_sub T p hcert hsub
      exact ⟨hlt, certificate_in hc hin hcer⟩
  · simp only [BoxTree.eval] at hnone
    split_ifs at hnone with hq
    · have hq' : InBox T.box.1 T.box.2 q := by rw [hbox]; exact hq
      obtain ⟨p, lo, hi', a, hsub, hin, heval⟩ := (balance_spec T hcov q).1 hq'
      rw [← hT, heval] at hnone
      subst hnone
      exact certificate_out hr.le hin (BSP.certified_sub T p hcert hsub j)
    · exact far_of_not_inBox hn0 P r hr hm q hq j
  · simp only [BoxTree.visits]
    split_ifs
    · have := (balance_spec T hcov q).2
      rw [← hT]
      have hlog : Nat.log 2 T.paths.card ≤ Nat.log 2 (2 * bspFuel n m δ) :=
        Nat.log_mono_right hsize
      omega
    · simp

end DetANN.HPIM

open DetANN.HPIM in
theorem solution {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n)
    (P : Fin n → EuclideanSpace ℝ (Fin m)) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    NearNbrSpec P r (1 + δ / 4) (lookupTree (fun i j => P i j) r (1 + δ / 4) δ) ∧
    ∀ q : Fin m → ℝ, (lookupTree (fun i j => P i j) r (1 + δ / 4) δ).visits q ≤
      5 * Nat.log 2 (2 * bspFuel n m δ) + 7 :=
  lookupTree_spec_aux hm hn P r δ hr hδ hδ'
