-- Prove2me | solution 1 for DemandResponse.SecondBest.lemmaA1_F0
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:12:05.398017+00:00
-- url     : https://prove2.me/submissions/87a2ccac-3488-4b58-a306-172f17b55362

import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian



namespace DemandResponse.SecondBest

lemma br_a_coord (μ A z a : ℝ) (hμ : 0 < μ) (hA : 0 < A) (ha0 : 0 ≤ a) (ha1 : a ≤ μ * A) :
    (μ * min (negp z) A) * z + (μ * min (negp z) A) ^ 2 / μ / 2 ≤ a * z + a ^ 2 / μ / 2 := by
  have key : μ * ((μ * min (negp z) A) * z + (μ * min (negp z) A) ^ 2 / μ / 2)
      ≤ μ * (a * z + a ^ 2 / μ / 2) := by
    have e1 : μ * ((μ * min (negp z) A) * z + (μ * min (negp z) A) ^ 2 / μ / 2)
        = μ * μ * min (negp z) A * z + (μ * min (negp z) A) ^ 2 / 2 := by
      field_simp
    have e2 : μ * (a * z + a ^ 2 / μ / 2) = μ * a * z + a ^ 2 / 2 := by field_simp
    rw [e1, e2]
    unfold negp
    rcases le_or_gt 0 z with hz | hz
    · have : max 0 (-z) = 0 := max_eq_left (by linarith)
      rw [this, min_eq_left hA.le]; nlinarith [mul_nonneg hμ.le ha0]
    · have : max 0 (-z) = -z := max_eq_right (by linarith)
      rw [this]
      rcases le_or_gt (-z) A with h2 | h2
      · rw [min_eq_left h2]; nlinarith [sq_nonneg (a + μ * z)]
      · rw [min_eq_right h2.le]
        nlinarith [mul_nonneg (sub_nonneg.2 ha1) hμ.le, mul_nonneg (sub_nonneg.2 ha1) ha0]
  exact le_of_mul_le_mul_left key hμ

lemma br_obj_a {N d : ℕ} (P : Params N d) (z : ℝ) (a : Fin N → ℝ) :
    (∑ i, a i) * z + c1 P a = ∑ i, (a i * z + a i ^ 2 / P.μ i / 2) := by
  unfold c1
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma ahat_mem {N d : ℕ} (P : Params N d) (z : ℝ) : ahat P z ∈ EffA P := by
  intro i
  have h0 : 0 ≤ min (negp z) P.Amax := le_min (le_max_left _ _) P.hAmax.le
  exact ⟨mul_nonneg (P.hμ i).le h0,
    mul_le_mul_of_nonneg_left (min_le_right _ _) (P.hμ i).le⟩

lemma ahat_opt {N d : ℕ} (P : Params N d) (z : ℝ) : ∀ a ∈ EffA P,
    (∑ i, ahat P z i) * z + c1 P (ahat P z) ≤ (∑ i, a i) * z + c1 P a := by
  intro a ha
  rw [br_obj_a, br_obj_a]
  exact Finset.sum_le_sum fun i _ =>
    br_a_coord (P.μ i) P.Amax z (a i) (P.hμ i) P.hAmax (ha i).1 (ha i).2

/-- rpow facts. -/
lemma rpow_half_facts (x : ℝ) (hx : 1 < x) :
    0 < x ^ (-(1 / 2 : ℝ)) ∧ x ^ (-(1 / 2 : ℝ)) < 1 ∧ x * (x ^ (-(1 / 2 : ℝ))) ^ 2 = 1 := by
  have hx0 : 0 < x := by linarith
  have e : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow]
  rw [e]
  have hs : 1 < Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  refine ⟨by positivity, inv_lt_one_of_one_lt₀ hs, ?_⟩
  rw [inv_pow, hsq]; field_simp

lemma br_b_coord (lam g ε b : ℝ) (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb0 : ε ≤ b) (hb1 : b ≤ 1) :
    let b0 := if lam * negp g ≤ 1 then 1 else max ε ((lam * negp g) ^ (-(1 / 2 : ℝ)))
    1 / lam * (b0⁻¹ - 1) - g * b0 ≤ 1 / lam * (b⁻¹ - 1) - g * b := by
  intro b0
  have hbp : 0 < b := lt_of_lt_of_le hε hb0
  set x := negp g with hxdef
  have hx0 : 0 ≤ x := le_max_left _ _
  have hgx : -g ≤ x := le_max_right _ _
  -- general reduction: suffices (b - b0) * (lam * x * b * b0 - 1) ≥ 0 when g = -x, or g ≥ 0
  have hb0pos : 0 < b0 ∧ ε ≤ b0 ∧ b0 ≤ 1 := by
    simp only [b0]
    split_ifs with h
    · exact ⟨one_pos, hε1, le_rfl⟩
    · push_neg at h
      obtain ⟨h1, h2, _⟩ := rpow_half_facts _ h
      exact ⟨lt_of_lt_of_le hε (le_max_left _ _), le_max_left _ _, max_le hε1 h2.le⟩
  obtain ⟨hp, hεb0, hb01⟩ := hb0pos
  rcases le_or_gt 0 g with hg | hg
  · have hx : x = 0 := by simp [hxdef, negp, hg]
    have hle : lam * negp g ≤ 1 := by rw [← hxdef, hx]; linarith
    have : b0 = 1 := by
      show (if lam * negp g ≤ 1 then _ else _) = 1
      rw [if_pos hle]
    rw [this]
    have : 1 / lam * (b⁻¹ - 1) ≥ 0 := by
      apply mul_nonneg (by positivity)
      rw [sub_nonneg]; exact one_le_inv₀ hbp |>.2 hb1
    have : g * b ≤ g * 1 := mul_le_mul_of_nonneg_left hb1 hg
    rw [inv_one, sub_self, mul_zero]; linarith
  · have hx : x = -g := by simp [hxdef, negp]; linarith
    have hg' : g = -x := by linarith
    rw [hg']
    -- multiply by lam * b * b0
    have key : (b - b0) * (lam * x * b * b0 - 1) ≥ 0 := by
      simp only [b0] at hp hεb0 hb01 ⊢
      split_ifs with h
      · have : lam * x * b * 1 ≤ 1 := by
          have : lam * x * b ≤ lam * x * 1 := mul_le_mul_of_nonneg_left hb1 (by positivity)
          linarith
        nlinarith
      · push_neg at h
        obtain ⟨h1, h2, h3⟩ := rpow_half_facts _ h
        set s := (lam * x) ^ (-(1 / 2 : ℝ))
        rcases le_or_gt s ε with hs | hs
        · rw [max_eq_left hs]
          have : lam * x * ε * ε ≥ 1 := by nlinarith [mul_le_mul hs hs h1.le hε.le]
          have : lam * x * b * ε ≥ lam * x * ε * ε := by
            have := mul_le_mul_of_nonneg_left hb0 (show 0 ≤ lam * x * ε by positivity)
            nlinarith
          nlinarith
        · rw [max_eq_right hs.le]
          have : (b - s) * (lam * x * b * s - 1) = lam * x * s * (b - s) ^ 2 := by
            linear_combination (b - s) * h3
          rw [this]; positivity
    have e : (1 / lam * (b⁻¹ - 1) - -x * b) - (1 / lam * (b0⁻¹ - 1) - -x * b0)
        = (b - b0) * (lam * x * b * b0 - 1) / (lam * b * b0) := by
      field_simp; ring
    have : (b - b0) * (lam * x * b * b0 - 1) / (lam * b * b0) ≥ 0 := by
      apply div_nonneg key; positivity
    linarith

lemma br_obj_b {N d : ℕ} (P : Params N d) (γ : ℝ) (b : Fin d → ℝ) :
    c2 P b - γ * sigmaSq P b = ∑ j, P.σ j ^ 2 * (1 / P.lam j * ((b j)⁻¹ - 1) - γ * b j) := by
  unfold c2 sigmaSq
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bhat_mem {N d : ℕ} (P : Params N d) (γ : ℝ) : bhat P γ ∈ EffB P := by
  intro j
  simp only [bhat]
  split_ifs with h
  · exact ⟨P.hε1, le_rfl⟩
  · push_neg at h
    obtain ⟨_, h2, _⟩ := rpow_half_facts _ h
    exact ⟨le_max_left _ _, max_le P.hε1 h2.le⟩

lemma bhat_opt {N d : ℕ} (P : Params N d) (γ : ℝ) : ∀ b ∈ EffB P,
    c2 P (bhat P γ) - γ * sigmaSq P (bhat P γ) ≤ c2 P b - γ * sigmaSq P b := by
  intro b hb
  rw [br_obj_b, br_obj_b]
  refine Finset.sum_le_sum fun j _ => ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact br_b_coord (P.lam j) γ P.ε (b j) (P.hlam j) P.hε P.hε1 (hb j).1 (hb j).2

theorem br_core {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, ahat P z ∈ EffA P ∧ ∀ a ∈ EffA P,
      (∑ i, ahat P z i) * z + c1 P (ahat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bhat P γ ∈ EffB P ∧ ∀ b ∈ EffB P,
      c2 P (bhat P γ) - γ * sigmaSq P (bhat P γ) ≤ c2 P b - γ * sigmaSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (negp z) P.Amax * negp z - min (negp z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2 P (bhat P γ) - γ * sigmaSq P (bhat P γ))) := by
  refine ⟨fun z => ⟨ahat_mem P z, ahat_opt P z⟩, fun γ => ⟨bhat_mem P γ, bhat_opt P γ⟩, ?_, ?_⟩
  · intro z
    have hl : IsLeast ((fun a => (∑ i, a i) * z + c1 P a) '' EffA P)
        ((∑ i, ahat P z i) * z + c1 P (ahat P z)) := by
      refine ⟨⟨_, ahat_mem P z, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact ahat_opt P z a ha
    unfold Hm
    rw [hl.csInf_eq, br_obj_a]
    simp only [ahat, muBar]
    have hm : min (negp z) P.Amax * z = - (min (negp z) P.Amax * negp z) := by
      unfold negp
      rcases le_or_gt 0 z with hz | hz
      · rw [max_eq_left (by linarith), min_eq_left P.hAmax.le]; ring
      · rw [max_eq_right (by linarith)]; ring
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := P.hμ i
    have e : (P.μ i * min (negp z) P.Amax) ^ 2 / P.μ i / 2
        = P.μ i * min (negp z) P.Amax ^ 2 / 2 := by field_simp
    rw [e]
    linear_combination (-P.μ i) * hm
  · intro γ
    have hl : IsLeast ((fun b => c2 P b - γ * sigmaSq P b) '' EffB P)
        (c2 P (bhat P γ) - γ * sigmaSq P (bhat P γ)) := by
      refine ⟨⟨_, bhat_mem P γ, rfl⟩, ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      exact bhat_opt P γ b hb
    unfold Hv
    rw [hl.csInf_eq]


theorem p21_core {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, ahat P z ∈ EffA P ∧
      ∀ a ∈ EffA P, (∑ i, ahat P z i) * z + c1 P (ahat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bhat P γ ∈ EffB P ∧
      ∀ b ∈ EffB P, c2 P (bhat P γ) - γ * sigmaSq P (bhat P γ) ≤ c2 P b - γ * sigmaSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (negp z) P.Amax * negp z - min (negp z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2hat P γ - γ * sigmaHatSq P γ)) := br_core P

lemma f0_opt {N d : ℕ} (P : Params N d) (q γ : ℝ) : f0 P q (-q) ≤ f0 P q γ := by
  have h := bhat_opt P (-q) (bhat P γ) (bhat_mem P γ)
  unfold f0 c2hat sigmaHatSq
  linarith

lemma bhat_negp {N d : ℕ} (P : Params N d) (γ : ℝ) : bhat P γ = bhat P (min γ 0) := by
  have : negp γ = negp (min γ 0) := by
    unfold negp
    rcases le_or_gt γ 0 with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h.le]; simp [max_eq_left (by linarith : -γ ≤ 0)]
  unfold bhat; rw [this]

lemma F0_eq {N d : ℕ} (P : Params N d) (q : ℝ) : F0 P q = f0 P q (-q) := by
  have hb : BddBelow (Set.range fun γ : {γ : ℝ // γ ≤ 0} => f0 P q γ) := by
    refine ⟨f0 P q (-q), ?_⟩
    rintro _ ⟨γ, rfl⟩
    exact f0_opt P q γ
  apply le_antisymm
  · have h1 := ciInf_le hb ⟨min (-q) 0, min_le_right _ _⟩
    have h2 : f0 P q (min (-q) 0) = f0 P q (-q) := by
      unfold f0 c2hat sigmaHatSq; rw [← bhat_negp]
    unfold F0; simp only at h1; linarith
  · unfold F0
    haveI : Nonempty {γ : ℝ // γ ≤ 0} := ⟨⟨0, le_rfl⟩⟩
    exact le_ciInf fun γ => f0_opt P q γ

lemma sigmaSq_nonneg {N d : ℕ} (P : Params N d) (b : Fin d → ℝ) (hb : b ∈ EffB P) :
    0 ≤ sigmaSq P b := by
  unfold sigmaSq
  exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (le_trans P.hε.le (hb j).1)

lemma sigmaSq_le {N d : ℕ} (P : Params N d) (b : Fin d → ℝ) (hb : b ∈ EffB P) :
    sigmaSq P b ≤ ∑ j, P.σ j ^ 2 := by
  unfold sigmaSq
  exact Finset.sum_le_sum fun j _ => by
    have := mul_le_mul_of_nonneg_left (hb j).2 (sq_nonneg (P.σ j)); linarith

/-- `F₀(q₁) ≤ F₀(q₂) + (q₁ - q₂) |σ̂(-q₂)|²`. -/
lemma F0_le {N d : ℕ} (P : Params N d) (q1 q2 : ℝ) :
    F0 P q1 ≤ F0 P q2 + (q1 - q2) * sigmaSq P (bhat P (-q2)) := by
  rw [F0_eq, F0_eq]
  have h := bhat_opt P (-q1) (bhat P (-q2)) (bhat_mem P _)
  unfold f0 c2hat sigmaHatSq
  linarith

lemma F0_mono {N d : ℕ} (P : Params N d) : Monotone (F0 P) := by
  intro q1 q2 hq
  have h := F0_le P q1 q2
  have := sigmaSq_nonneg P _ (bhat_mem P (-q2))
  nlinarith

lemma F0_cont {N d : ℕ} (P : Params N d) : Continuous (F0 P) := by
  apply LipschitzWith.continuous (K := ⟨∑ j, P.σ j ^ 2,
    Finset.sum_nonneg fun j _ => sq_nonneg _⟩)
  apply LipschitzWith.of_le_add_mul
  intro q1 q2
  have h := F0_le P q1 q2
  have h0 := sigmaSq_nonneg P _ (bhat_mem P (-q2))
  have h1 := sigmaSq_le P _ (bhat_mem P (-q2))
  simp only [NNReal.coe_mk, Real.dist_eq]
  have hS : 0 ≤ ∑ j, P.σ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have : (q1 - q2) * sigmaSq P (bhat P (-q2)) ≤ (∑ j, P.σ j ^ 2) * |q1 - q2| := by
    calc (q1 - q2) * sigmaSq P (bhat P (-q2)) ≤ |q1 - q2| * sigmaSq P (bhat P (-q2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |q1 - q2| * ∑ j, P.σ j ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := by ring
  show F0 P q1 ≤ F0 P q2 + (∑ j, P.σ j ^ 2) * |q1 - q2|
  linarith

theorem a1_core {N d : ℕ} (P : Params N d) :
    (∀ q : ℝ, F0 P q = f0 P q (-q) ∧ f0 P q (-q) = -2 * Hv P (-q)) ∧ Monotone (F0 P) := by
  refine ⟨fun q => ⟨F0_eq P q, ?_⟩, F0_mono P⟩
  rw [(br_core P).2.2.2 (-q)]
  unfold f0 c2hat sigmaHatSq; ring

lemma muBar_nonneg {N d : ℕ} (P : Params N d) : 0 ≤ muBar P :=
  Finset.sum_nonneg fun i _ => (P.hμ i).le

theorem a4_core {N d : ℕ} (P : Params N d) (y k : ℝ) :
    let Φ : ℝ → ℝ := fun z =>
      F0 P (P.h - k + P.r * z ^ 2 + P.p * (z - y) ^ 2) + muBar P * (negp z + y) ^ 2
    (0 ≤ y → IsMinOn Φ Set.univ (P.p / (P.r + P.p) * y)) ∧
    (y ≤ 0 → ∃ z ∈ Set.Icc y (P.p / (P.r + P.p) * y), IsMinOn Φ Set.univ z) := by
  intro Φ
  have hr := P.hr
  have hp := P.hp
  have hm := muBar_nonneg P
  set zs := P.p / (P.r + P.p) * y with hzs
  have hzs' : (P.r + P.p) * zs = P.p * y := by rw [hzs]; field_simp
  -- Q(z) - Q(zs) = (r+p)(z - zs)^2
  have hQ : ∀ z, P.r * z ^ 2 + P.p * (z - y) ^ 2 =
      P.r * zs ^ 2 + P.p * (zs - y) ^ 2 + (P.r + P.p) * (z - zs) ^ 2 := by
    intro z; linear_combination (2 * z - 2 * zs) * hzs'
  have hQmin : ∀ z, P.h - k + P.r * zs ^ 2 + P.p * (zs - y) ^ 2 ≤
      P.h - k + P.r * z ^ 2 + P.p * (z - y) ^ 2 := by
    intro z; have := hQ z; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.r + P.p) (sq_nonneg (z - zs))]
  constructor
  · intro hy
    have hzs0 : 0 ≤ zs := by rw [hzs]; positivity
    intro z _
    show Φ zs ≤ Φ z
    simp only [Φ]
    have e1 : negp zs = 0 := by unfold negp; exact max_eq_left (by linarith)
    have e2 : y ^ 2 ≤ (negp z + y) ^ 2 := by
      have : 0 ≤ negp z := le_max_left _ _
      nlinarith
    rw [e1, zero_add]
    have := F0_mono P (hQmin z)
    nlinarith
  · intro hy
    have hzsy : y ≤ zs := by
      rw [hzs]
      have : P.p / (P.r + P.p) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have hzs0 : zs ≤ 0 := by rw [hzs]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hy
    have hcont : Continuous Φ := by
      simp only [Φ]
      unfold negp
      exact ((F0_cont P).comp (by fun_prop)).add (by fun_prop)
    obtain ⟨z0, hz0, hmin⟩ := (isCompact_Icc (a := y) (b := zs)).exists_isMinOn
      (Set.nonempty_Icc.2 hzsy) hcont.continuousOn
    refine ⟨z0, hz0, fun z _ => ?_⟩
    have hy_le := hmin (Set.left_mem_Icc.2 hzsy)
    have hzs_le := hmin (Set.right_mem_Icc.2 hzsy)
    simp only [Set.mem_setOf_eq] at hy_le hzs_le ⊢
    rcases le_or_gt z y with h1 | h1
    · -- Φ z ≥ Φ y
      refine le_trans hy_le ?_
      simp only [Φ]
      have ey : negp y = -y := by unfold negp; exact max_eq_right (by linarith)
      have ez : negp z = -z := by unfold negp; exact max_eq_right (by linarith)
      rw [ey, ez]
      have hQ' : P.h - k + P.r * y ^ 2 + P.p * (y - y) ^ 2 ≤
          P.h - k + P.r * z ^ 2 + P.p * (z - y) ^ 2 := by
        have a := hQ z; have b := hQ y
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.r + P.p)
          (mul_nonneg (by linarith : (0:ℝ) ≤ zs - y) (by linarith : (0:ℝ) ≤ y - z)),
          mul_nonneg (by linarith : (0:ℝ) ≤ P.r + P.p)
          (mul_nonneg (by linarith : (0:ℝ) ≤ y - z) (by linarith : (0:ℝ) ≤ y - z))]
      have := F0_mono P hQ'
      nlinarith [sq_nonneg (-z + y)]
    rcases le_or_gt z zs with h4 | h4
    · exact hmin ⟨h1.le, h4⟩
    refine le_trans hzs_le ?_
    simp only [Φ]
    have ezs : negp zs = -zs := by unfold negp; exact max_eq_right (by linarith)
    have hF := F0_mono P (hQmin z)
    have hsq : (-zs + y) ^ 2 ≤ (negp z + y) ^ 2 := by
      have hrs : -zs + y ≤ 0 := by linarith
      rcases le_or_gt z 0 with h2 | h2
      · have ez : negp z = -z := by unfold negp; exact max_eq_right (by linarith)
        rw [ez]; nlinarith
      · have ez : negp z = 0 := by unfold negp; exact max_eq_left (by linarith)
        rw [ez]
        nlinarith
    rw [ezs]
    nlinarith

end DemandResponse.SecondBest

open DemandResponse.SecondBest


theorem solution {N d : ℕ} (P : Params N d) :
    (∀ q : ℝ, F0 P q = f0 P q (-q) ∧ f0 P q (-q) = -2 * Hv P (-q)) ∧ Monotone (F0 P) := by
  exact a1_core P
