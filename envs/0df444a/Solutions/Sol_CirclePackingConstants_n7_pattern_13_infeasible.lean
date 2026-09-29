-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_13_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:36:08.613667+00:00
-- url     : https://prove2.me/submissions/77351095-6f72-4266-922d-72532b19f2a2

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_CirclePackingConstants_n7_rep13_localization
import Theorems.Thm_CirclePackingConstants_n7_six_core_rigidity
noncomputable section
namespace CirclePackingConstants

lemma abs_near_one {x : ℝ} (hxL : (2970:ℝ) ≤ x) (hxU : x ≤ 3000) : |1-x/3000| ≤ 1/100 := by
  rw [abs_le]
  constructor <;> linarith only [hxL, hxU]

lemma abs_near_zero {x : ℝ} (hxL : (0:ℝ) ≤ x) (hxU : x ≤ 5) : |x/3000| ≤ 1/100 := by
  rw [abs_le]
  constructor <;> linarith only [hxL, hxU]

lemma abs_near_sep {x s : ℝ} (hxL : (1388:ℝ) ≤ x) (hxU : x ≤ 1393)
    (hsL : (0.53:ℝ) < s) (hsU : s < 0.54) :
    |1-x/3000-s| ≤ 1/100 := by
  rw [abs_le]
  constructor <;> linarith only [hxL, hxU, hsL, hsU]

lemma abs_near_half {x s : ℝ} (hxL : (2190:ℝ) ≤ x) (hxU : x ≤ 2198)
    (hsL : (0.53:ℝ) < s) (hsU : s < 0.54) :
    |1-x/3000-s/2| ≤ 1/100 := by
  rw [abs_le]
  constructor <;> linarith only [hxL, hxU, hsL, hsU]

lemma n7_rep13_bounds
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000) :
 ∃ (r s a b c e f g h i j k l t M : ℝ),
  r = Real.sqrt 3 ∧ s = 4 - 2*r ∧ r^2 = 3 ∧
  a = 1-x6/3000 ∧ b = 1-y6/3000 ∧ c = 1-x5/3000-s ∧ e = 1-y5/3000 ∧
  f = -x4/3000 ∧ g = 1-y4/3000-s/2 ∧ h = 1-x3/3000 ∧ i = 1-y3/3000-s ∧
  j = 1-x2/3000-s ∧ k = 1-y2/3000-s ∧ l = 1-x1/3000-s/2 ∧ t = -y1/3000 ∧
  M = max |a| (max |b| (max |c| (max |e| (max |f| (max |g| (max |h| (max |i| (max |j| (max |k| (max |l| |t|)))))))))) ∧
  (|a| ≤ 1/100 ∧ |b| ≤ 1/100 ∧ |c| ≤ 1/100 ∧ |e| ≤ 1/100 ∧
   |f| ≤ 1/100 ∧ |g| ≤ 1/100 ∧ |h| ≤ 1/100 ∧ |i| ≤ 1/100 ∧
   |j| ≤ 1/100 ∧ |k| ≤ 1/100 ∧ |l| ≤ 1/100 ∧ |t| ≤ 1/100) ∧
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ e ∧ 0 ≤ h ∧ f ≤ 0 ∧ t ≤ 0 ∧ 0 ≤ M ∧ M ≤ 1/100 := by
  let r : ℝ := Real.sqrt 3
  let s : ℝ := 4 - 2*r
  let a : ℝ := 1-x6/3000
  let b : ℝ := 1-y6/3000
  let c : ℝ := 1-x5/3000-s
  let e : ℝ := 1-y5/3000
  let f : ℝ := -x4/3000
  let g : ℝ := 1-y4/3000-s/2
  let h : ℝ := 1-x3/3000
  let i : ℝ := 1-y3/3000-s
  let j : ℝ := 1-x2/3000-s
  let k : ℝ := 1-y2/3000-s
  let l : ℝ := 1-x1/3000-s/2
  let t : ℝ := -y1/3000
  have hr0 : 0 ≤ r := by dsimp [r]; exact Real.sqrt_nonneg _
  have hr2 : r^2 = (3:ℝ) := by dsimp [r]; rw [Real.sq_sqrt] <;> norm_num
  have hrL : (1.73:ℝ) < r := by nlinarith
  have hrU : r < (1.735:ℝ) := by nlinarith
  have hsL : (0.53:ℝ) < s := by dsimp [s]; nlinarith
  have hsU : s < (0.54:ℝ) := by dsimp [s]; nlinarith
  have ha : |a| ≤ 1/100 := by
    apply abs_near_one
    · linarith only [hx6L]
    · exact hx6U
  have hb : |b| ≤ 1/100 := by
    apply abs_near_one
    · linarith only [hy6L]
    · exact hy6U
  have hc : |c| ≤ 1/100 := by
    apply abs_near_sep hx5L hx5U hsL hsU
  have he : |e| ≤ 1/100 := by
    have hdiv := div_le_div_of_nonneg_right hy5U (by norm_num : (0:ℝ) ≤ 3000)
    have he' : 0 ≤ 1 - y5 / 3000 := sub_nonneg.mpr (by simpa using hdiv)
    have hdivLower := div_le_div_of_nonneg_right hy5L (by norm_num : (0:ℝ) ≤ 3000)
    have hratio : (99:ℝ)/100 ≤ y5 / 3000 := by nlinarith only [hdivLower]
    have he'' : 1 - y5 / 3000 ≤ 1/100 := by linarith only [hratio]
    have heLow : -(1/100:ℝ) ≤ 1 - y5 / 3000 := by linarith only [he']
    have heLow' : -(1/100:ℝ) ≤ 1 - y5 / 3000 := by norm_num at heLow ⊢; exact heLow
    simpa [e] using (abs_le).2 ⟨heLow', he''⟩
  have hf0 := abs_near_zero hx4L hx4U
  have hf : |f| ≤ 1/100 := by
    calc
      |f| = |x4 / 3000| := by dsimp [f]; rw [neg_div, abs_neg]
      _ ≤ 1/100 := hf0
  have hg : |g| ≤ 1/100 := by
    apply abs_near_half hy4L hy4U hsL hsU
  have hh : |h| ≤ 1/100 := by
    apply abs_near_one
    · linarith only [hx3L]
    · exact hx3U
  have hi : |i| ≤ 1/100 := by
    apply abs_near_sep hy3L hy3U hsL hsU
  have hj : |j| ≤ 1/100 := by
    apply abs_near_sep hx2L hx2U hsL hsU
  have hk : |k| ≤ 1/100 := by
    apply abs_near_sep hy2L hy2U hsL hsU
  have hl : |l| ≤ 1/100 := by
    apply abs_near_half hx1L hx1U hsL hsU
  have ht0 := abs_near_zero hy1L hy1U
  have ht : |t| ≤ 1/100 := by
    calc
      |t| = |y1 / 3000| := by dsimp [t]; rw [neg_div, abs_neg]
      _ ≤ 1/100 := ht0
  let M : ℝ := max |a| (max |b| (max |c| (max |e| (max |f| (max |g| (max |h| (max |i| (max |j| (max |k| (max |l| |t|))))))))))
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact le_trans (abs_nonneg a) (le_max_left _ _)
  have hM : M ≤ 1/100 := by
    dsimp [M]
    exact max_le ha (max_le hb (max_le hc (max_le he (max_le hf (max_le hg (max_le hh (max_le hi (max_le hj (max_le hk (max_le hl ht))))))))))
  refine ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M, rfl, rfl, hr2,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨ha,hb,hc,he,hf,hg,hh,hi,hj,hk,hl,ht⟩
  · dsimp [a]; linarith only [hx6U]
  · dsimp [b]; linarith only [hy6U]
  · have hdiv : y5 / 3000 ≤ (1:ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0:ℝ) < 3000)).2
      linarith only [hy5U]
    have he' : 0 ≤ 1 - y5 / 3000 := sub_nonneg.mpr hdiv
    simpa [e] using he' 
  · dsimp [h]; linarith only [hx3U]
  · dsimp [f]; linarith only [hx4L]
  · dsimp [t]; linarith only [hy1L]
  · exact hM0
  · exact hM
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_max_bounds
 (a b c e f g h i j k l t M : ℝ)
 (hmax : M = max |a| (max |b| (max |c| (max |e| (max |f| (max |g| (max |h| (max |i| (max |j| (max |k| (max |l| |t|))))))))))) :
 (-M ≤ a ∧ a ≤ M) ∧ (-M ≤ b ∧ b ≤ M) ∧ (-M ≤ c ∧ c ≤ M) ∧
 (-M ≤ e ∧ e ≤ M) ∧ (-M ≤ f ∧ f ≤ M) ∧ (-M ≤ g ∧ g ≤ M) ∧
 (-M ≤ h ∧ h ≤ M) ∧ (-M ≤ i ∧ i ≤ M) ∧ (-M ≤ j ∧ j ≤ M) ∧
 (-M ≤ k ∧ k ≤ M) ∧ (-M ≤ l ∧ l ≤ M) ∧ (-M ≤ t ∧ t ≤ M) := by
  have ha : |a| ≤ M := by simpa [hmax]
  have hb : |b| ≤ M := by simpa [hmax]
  have hc : |c| ≤ M := by simpa [hmax]
  have he : |e| ≤ M := by simpa [hmax]
  have hf : |f| ≤ M := by simpa [hmax]
  have hg : |g| ≤ M := by simpa [hmax]
  have hh : |h| ≤ M := by simpa [hmax]
  have hi : |i| ≤ M := by simpa [hmax]
  have hj : |j| ≤ M := by simpa [hmax]
  have hk : |k| ≤ M := by simpa [hmax]
  have hl : |l| ≤ M := by simpa [hmax]
  have ht : |t| ≤ M := by simpa [hmax]
  exact ⟨(abs_le.mp ha), (abs_le.mp hb), (abs_le.mp hc), (abs_le.mp he),
    (abs_le.mp hf), (abs_le.mp hg), (abs_le.mp hh), (abs_le.mp hi),
    (abs_le.mp hj), (abs_le.mp hk), (abs_le.mp hl), (abs_le.mp ht)⟩
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_constants (r s : ℝ)
    (hr : r = Real.sqrt 3) (hs : s = 4 - 2*r) (hr2 : r^2 = 3) :
    0 ≤ r ∧ (3:ℝ)/2 ≤ r ∧ r ≤ 9/5 ∧ (1:ℝ)/2 < s ∧ 2*(1-s)=r*s := by
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact Real.sqrt_nonneg _
  have hr15 : (3:ℝ)/2 ≤ r := by
    nlinarith only [hr2, hr0]
  have hr18 : r ≤ (9:ℝ)/5 := by
    nlinarith only [hr2, hr0]
  have hr175 : r < (7:ℝ)/4 := by nlinarith only [hr2, hr0]
  have hsHalf : (1:ℝ)/2 < s := by
    rw [hs]
    nlinarith only [hr175]
  have hrel : 2*(1-s)=r*s := by
    rw [hs]
    nlinarith only [hr2]
  exact ⟨hr0, hr15, hr18, hsHalf, hrel⟩
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C1_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep56 : (4-2*Real.sqrt 3)^2 < ((x5-x6)/3000)^2 + ((y5-y6)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ (4-2*Real.sqrt 3 + (1-x5/3000-(4-2*Real.sqrt 3)) - (1-x6/3000))^2 + ((1-y5/3000) - (1-y6/3000))^2 := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (s+c-a)^2+(e-b)^2 = ((x5-x6)/3000)^2+((y5-y6)/3000)^2 := by
    rw [hca, hcc, hba, hee]
    ring
  have C1 : s^2 ≤ (s+c-a)^2+(e-b)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep56)
  simpa [hs, hr, hca, hba, hcc, hee] using C1
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C2_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep36 : (4-2*Real.sqrt 3)^2 < ((x3-x6)/3000)^2 + ((y3-y6)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ ((1-x3/3000) - (1-x6/3000))^2 + ((4-2*Real.sqrt 3) + (1-y3/3000-(4-2*Real.sqrt 3)) - (1-y6/3000))^2 := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (h-a)^2+(s+i-b)^2 = ((x3-x6)/3000)^2+((y3-y6)/3000)^2 := by
    rw [hhh, hca, hii, hba]
    ring
  have C2 : s^2 ≤ (h-a)^2+(s+i-b)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep36)
  simpa [hs, hr, hhh, hca, hii, hba] using C2
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C3_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep52 : (4-2*Real.sqrt 3)^2 < ((x5-x2)/3000)^2 + ((y5-y2)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ ((1-x2/3000-(4-2*Real.sqrt 3)) - (1-x5/3000-(4-2*Real.sqrt 3)))^2 + ((4-2*Real.sqrt 3) + (1-y2/3000-(4-2*Real.sqrt 3)) - (1-y5/3000))^2 := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (j-c)^2+(s+k-e)^2 = ((x5-x2)/3000)^2+((y5-y2)/3000)^2 := by
    rw [hjj, hcc, hkk, hee]
    ring
  have C3 : s^2 ≤ (j-c)^2+(s+k-e)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep52)
  simpa [hs, hr, hjj, hcc, hkk, hee] using C3
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C4_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep32 : (4-2*Real.sqrt 3)^2 < ((x3-x2)/3000)^2 + ((y3-y2)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ ((4-2*Real.sqrt 3 + (1-x2/3000-(4-2*Real.sqrt 3)) - (1-x3/3000))^2 + ((1-y2/3000-(4-2*Real.sqrt 3)) - (1-y3/3000-(4-2*Real.sqrt 3)))^2) := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (s+j-h)^2+(k-i)^2 = ((x3-x2)/3000)^2+((y3-y2)/3000)^2 := by
    rw [hjj, hhh, hkk, hii]
    ring
  have C4 : s^2 ≤ (s+j-h)^2+(k-i)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep32)
  simpa [hs, hr, hjj, hhh, hkk, hii] using C4
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C5_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep54 : (4-2*Real.sqrt 3)^2 < ((x5-x4)/3000)^2 + ((y5-y4)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ (1-(4-2*Real.sqrt 3)+(-x4/3000)-(1-x5/3000-(4-2*Real.sqrt 3)))^2 + ((4-2*Real.sqrt 3)/2 + (1-y4/3000-(4-2*Real.sqrt 3)/2) - (1-y5/3000))^2 := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (1-s+f-c)^2+(s/2+g-e)^2 = ((x5-x4)/3000)^2+((y5-y4)/3000)^2 := by
    rw [hff, hcc, hgg, hee]
    ring
  have C5 : s^2 ≤ (1-s+f-c)^2+(s/2+g-e)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep54)
  simpa [hs, hr, hff, hcc, hgg, hee] using C5
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C6_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep24 : (4-2*Real.sqrt 3)^2 < ((x2-x4)/3000)^2 + ((y2-y4)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ (1-(4-2*Real.sqrt 3)+(-x4/3000)-(1-x2/3000-(4-2*Real.sqrt 3)))^2 + (-(4-2*Real.sqrt 3)/2 + (1-y4/3000-(4-2*Real.sqrt 3)/2) - (1-y2/3000-(4-2*Real.sqrt 3)))^2 := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (1-s+f-j)^2+(-s/2+g-k)^2 = ((x2-x4)/3000)^2+((y2-y4)/3000)^2 := by
    rw [hff, hjj, hgg, hkk]
    ring
  have C6 : s^2 ≤ (1-s+f-j)^2+(-s/2+g-k)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep24)
  simpa [hs, hr, hff, hjj, hgg, hkk] using C6
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C7_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep31 : (4-2*Real.sqrt 3)^2 < ((x3-x1)/3000)^2 + ((y3-y1)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ ((4-2*Real.sqrt 3)/2 + (1-x1/3000-(4-2*Real.sqrt 3)/2) - (1-x3/3000))^2 + (1-(4-2*Real.sqrt 3) + (-y1/3000) - (1-y3/3000-(4-2*Real.sqrt 3)))^2 := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (s/2+l-h)^2+(1-s+t-i)^2 = ((x3-x1)/3000)^2+((y3-y1)/3000)^2 := by
    rw [hll, hhh, htt, hii]
    ring
  have C7 : s^2 ≤ (s/2+l-h)^2+(1-s+t-i)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep31)
  simpa [hs, hr, hll, hhh, htt, hii] using C7
end CirclePackingConstants
namespace CirclePackingConstants
lemma n7_rep13_C8_test
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep21 : (4-2*Real.sqrt 3)^2 < ((x2-x1)/3000)^2 + ((y2-y1)/3000)^2) :
 (4-2*Real.sqrt 3)^2 ≤ (-(4-2*Real.sqrt 3)/2 + (1-x1/3000-(4-2*Real.sqrt 3)/2) - (1-x2/3000-(4-2*Real.sqrt 3)))^2 + (1-(4-2*Real.sqrt 3) + (-y1/3000) - (1-y2/3000-(4-2*Real.sqrt 3)))^2 := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hMdef,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  have hid : (-s/2+l-j)^2+(1-s+t-k)^2 = ((x2-x1)/3000)^2+((y2-y1)/3000)^2 := by
    rw [hll, hjj, htt, hkk]
    ring
  have C8 : s^2 ≤ (-s/2+l-j)^2+(1-s+t-k)^2 := by
    rw [hid]
    exact le_of_lt (by simpa [hr, hs] using hSep21)
  simpa [hs, hr, hll, hjj, htt, hkk] using C8
end CirclePackingConstants

namespace CirclePackingConstants

lemma n7_rep13_core_bridge
 (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx1L : (2190:ℝ) ≤ x1) (hx1U : x1 ≤ 2198) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ 5)
 (hx2L : (1388:ℝ) ≤ x2) (hx2U : x2 ≤ 1393) (hy2L : (1388:ℝ) ≤ y2) (hy2U : y2 ≤ 1393)
 (hx3L : (2995:ℝ) ≤ x3) (hx3U : x3 ≤ 3000) (hy3L : (1388:ℝ) ≤ y3) (hy3U : y3 ≤ 1393)
 (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ 5) (hy4L : (2190:ℝ) ≤ y4) (hy4U : y4 ≤ 2198)
 (hx5L : (1388:ℝ) ≤ x5) (hx5U : x5 ≤ 1393) (hy5L : (2995:ℝ) ≤ y5) (hy5U : y5 ≤ 3000)
 (hx6L : (2995:ℝ) ≤ x6) (hx6U : x6 ≤ 3000) (hy6L : (2995:ℝ) ≤ y6) (hy6U : y6 ≤ 3000)
 (hSep56 : (4-2*Real.sqrt 3)^2 < ((x5-x6)/3000)^2 + ((y5-y6)/3000)^2)
 (hSep36 : (4-2*Real.sqrt 3)^2 < ((x3-x6)/3000)^2 + ((y3-y6)/3000)^2)
 (hSep52 : (4-2*Real.sqrt 3)^2 < ((x5-x2)/3000)^2 + ((y5-y2)/3000)^2)
 (hSep32 : (4-2*Real.sqrt 3)^2 < ((x3-x2)/3000)^2 + ((y3-y2)/3000)^2)
 (hSep54 : (4-2*Real.sqrt 3)^2 < ((x5-x4)/3000)^2 + ((y5-y4)/3000)^2)
 (hSep24 : (4-2*Real.sqrt 3)^2 < ((x2-x4)/3000)^2 + ((y2-y4)/3000)^2)
 (hSep31 : (4-2*Real.sqrt 3)^2 < ((x3-x1)/3000)^2 + ((y3-y1)/3000)^2)
 (hSep21 : (4-2*Real.sqrt 3)^2 < ((x2-x1)/3000)^2 + ((y2-y1)/3000)^2) : False := by
  obtain ⟨r,s,a,b,c,e,f,g,h,i,j,k,l,t,M,hr,hs,hr2,hca,hba,hcc,hee,hff,hgg,hhh,hii,hjj,hkk,hll,htt,hmax,habs,haS,hbS,heS,hhS,hfS,htS,hM0,hM⟩ :=
    n7_rep13_bounds x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
      hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U
      hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U
  obtain ⟨haB,hbB,hcB,heB,hfB,hgB,hhB,hiB,hjB,hkB,hlB,htB⟩ :=
    n7_rep13_max_bounds a b c e f g h i j k l t M hmax
  obtain ⟨hr0,hr15,hr18,hs_half,hrel⟩ := n7_rep13_constants r s hr hs hr2
  have hs0 : 0 < s := by linarith
  let eta : ℝ := 4 * M^2 / s
  have heta : eta = 4 * M^2 / s := rfl
  have C1raw := n7_rep13_C1_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep56
  have C2raw := n7_rep13_C2_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep36
  have C3raw := n7_rep13_C3_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep52
  have C4raw := n7_rep13_C4_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep32
  have C5raw := n7_rep13_C5_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep54
  have C6raw := n7_rep13_C6_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep24
  have C7raw := n7_rep13_C7_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep31
  have C8raw := n7_rep13_C8_test x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hSep21
  have C1 : s^2 ≤ (s+c-a)^2+(e-b)^2 := by simpa [hs, hr, hca, hba, hcc, hee] using C1raw
  have C2 : s^2 ≤ (h-a)^2+(s+i-b)^2 := by simpa [hs, hr, hhh, hca, hii, hba] using C2raw
  have C3 : s^2 ≤ (j-c)^2+(s+k-e)^2 := by simpa [hs, hr, hjj, hcc, hkk, hee] using C3raw
  have C4 : s^2 ≤ (s+j-h)^2+(k-i)^2 := by simpa [hs, hr, hjj, hhh, hkk, hii] using C4raw
  have C5 : s^2 ≤ (1-s+f-c)^2+(s/2+g-e)^2 := by simpa [hs, hr, hff, hcc, hgg, hee] using C5raw
  have C6 : s^2 ≤ (1-s+f-j)^2+(-s/2+g-k)^2 := by simpa [hs, hr, hff, hjj, hgg, hkk] using C6raw
  have C7 : s^2 ≤ (s/2+l-h)^2+(1-s+t-i)^2 := by simpa [hs, hr, hll, hhh, htt, hii] using C7raw
  have C8 : s^2 ≤ (-s/2+l-j)^2+(1-s+t-k)^2 := by simpa [hs, hr, hll, hjj, htt, hkk] using C8raw
  obtain ⟨za,zb,zc,ze,zf,zg,zh,zi,zj,zk,zl,zt⟩ := CirclePackingConstants.n7_six_core_rigidity s r M eta a b c e f g h i j k l t
    hs0 hs_half hr0 hr15 hr18 hr2 hrel hM0 hM heta hmax
    haB.1 haB.2 hbB.1 hbB.2 hcB.1 hcB.2 heB.1 heB.2 hfB.1 hfB.2 hgB.1 hgB.2 hhB.1 hhB.2 hiB.1 hiB.2 hjB.1 hjB.2 hkB.1 hkB.2 hlB.1 hlB.2 htB.1 htB.2
    haS hbS heS hhS hfS htS C1 C2 C3 C4 C5 C6 C7 C8
  have hid : (s+c-a)^2+(e-b)^2 = ((x5-x6)/3000)^2+((y5-y6)/3000)^2 := by
    rw [hca, hcc, hba, hee]
    ring
  have hstrict : s^2 < (s+c-a)^2+(e-b)^2 := by
    rw [hid]
    simpa [hr, hs] using hSep56
  rw [za, zc, ze, zb] at hstrict
  nlinarith only [hstrict]
end CirclePackingConstants
open CirclePackingConstants
theorem solution
 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L : (0:ℝ) ≤ x0)
 (hx0U : x0 ≤ (1000:ℝ))
 (hy0L : (0:ℝ) ≤ y0)
 (hy0U : y0 ≤ (1000:ℝ))
 (hx1L : (2000:ℝ) ≤ x1)
 (hx1U : x1 ≤ (3000:ℝ))
 (hy1L : (0:ℝ) ≤ y1)
 (hy1U : y1 ≤ (1000:ℝ))
 (hx2L : (1000:ℝ) ≤ x2)
 (hx2U : x2 ≤ (2000:ℝ))
 (hy2L : (1000:ℝ) ≤ y2)
 (hy2U : y2 ≤ (2000:ℝ))
 (hx3L : (2000:ℝ) ≤ x3)
 (hx3U : x3 ≤ (3000:ℝ))
 (hy3L : (1000:ℝ) ≤ y3)
 (hy3U : y3 ≤ (2000:ℝ))
 (hx4L : (0:ℝ) ≤ x4)
 (hx4U : x4 ≤ (1000:ℝ))
 (hy4L : (2000:ℝ) ≤ y4)
 (hy4U : y4 ≤ (3000:ℝ))
 (hx5L : (1000:ℝ) ≤ x5)
 (hx5U : x5 ≤ (2000:ℝ))
 (hy5L : (2000:ℝ) ≤ y5)
 (hy5U : y5 ≤ (3000:ℝ))
 (hx6L : (2000:ℝ) ≤ x6)
 (hx6U : x6 ≤ (3000:ℝ))
 (hy6L : (2000:ℝ) ≤ y6)
 (hy6U : y6 ≤ (3000:ℝ))
  (hT01 : (2584683:ℝ) < (x0-x1)^2+(y0-y1)^2)
  (hT02 : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2)
  (hT03 : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2)
  (hT04 : (2584683:ℝ) < (x0-x4)^2+(y0-y4)^2)
  (hT05 : (2584683:ℝ) < (x0-x5)^2+(y0-y5)^2)
  (hT06 : (2584683:ℝ) < (x0-x6)^2+(y0-y6)^2)
  (hT12 : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2)
  (hT13 : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2)
  (hT14 : (2584683:ℝ) < (x1-x4)^2+(y1-y4)^2)
  (hT15 : (2584683:ℝ) < (x1-x5)^2+(y1-y5)^2)
  (hT16 : (2584683:ℝ) < (x1-x6)^2+(y1-y6)^2)
  (hT23 : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2)
  (hT24 : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2)
  (hT25 : (2584683:ℝ) < (x2-x5)^2+(y2-y5)^2)
  (hT26 : (2584683:ℝ) < (x2-x6)^2+(y2-y6)^2)
  (hT34 : (2584683:ℝ) < (x3-x4)^2+(y3-y4)^2)
  (hT35 : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2)
  (hT36 : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2)
  (hT45 : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2)
  (hT46 : (2584683:ℝ) < (x4-x6)^2+(y4-y6)^2)
  (hT56 : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2)
 (hSep56 : (4-2*Real.sqrt 3)^2 < ((x5-x6)/3000)^2 + ((y5-y6)/3000)^2)
 (hSep36 : (4-2*Real.sqrt 3)^2 < ((x3-x6)/3000)^2 + ((y3-y6)/3000)^2)
 (hSep52 : (4-2*Real.sqrt 3)^2 < ((x5-x2)/3000)^2 + ((y5-y2)/3000)^2)
 (hSep32 : (4-2*Real.sqrt 3)^2 < ((x3-x2)/3000)^2 + ((y3-y2)/3000)^2)
 (hSep54 : (4-2*Real.sqrt 3)^2 < ((x5-x4)/3000)^2 + ((y5-y4)/3000)^2)
 (hSep24 : (4-2*Real.sqrt 3)^2 < ((x2-x4)/3000)^2 + ((y2-y4)/3000)^2)
 (hSep31 : (4-2*Real.sqrt 3)^2 < ((x3-x1)/3000)^2 + ((y3-y1)/3000)^2)
 (hSep21 : (4-2*Real.sqrt 3)^2 < ((x2-x1)/3000)^2 + ((y2-y1)/3000)^2)
 : False  := by
  rcases CirclePackingConstants.n7_rep13_localization x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 hx0L hx0U hy0L hy0U hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s7_0,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s7_7,s7_8,s7_9,s7_10,s7_11,s7_12,s7_13,s7_14,s7_15,s7_16,s7_17,s7_18,s7_19,s7_20,s7_21,s7_22,s7_23,s7_24,s7_25,s7_26,s7_27⟩
  exact n7_rep13_core_bridge x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6
    s7_4 s7_5 s7_6 s7_7 s7_8 s7_9 s7_10 s7_11 s7_12 s7_13 s7_14 s7_15 s7_16 s7_17 s7_18 s7_19 s7_20 s7_21 s7_22 s7_23 s7_24 s7_25 s7_26 s7_27
    hSep56 hSep36 hSep52 hSep32 hSep54 hSep24 hSep31 hSep21
