-- Prove2me | solution 1 for ChenSimchiLevi.Additive.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T01:22:03.210188+00:00
-- url     : https://prove2.me/submissions/9766e2e8-0df4-4e25-bbdb-7eeac1c4db1f

-- Licensed under Apache 2.0. Full exact theorem: additive-demand optimal inventory and pricing policy.
import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_Model


namespace ChenProof

def growthWeight (ρ : ℕ) (x : ℝ) : ℝ := 1 + |x| + |x| ^ ρ

def growthFactor (ρ : ℕ) : ℝ := 2 ^ (ρ - 1) + 1

lemma growthWeight_ge_one (ρ : ℕ) (x : ℝ) : 1 ≤ growthWeight ρ x := by
  unfold growthWeight
  linarith [abs_nonneg x, pow_nonneg (abs_nonneg x) ρ]

lemma growthWeight_nonneg (ρ : ℕ) (x : ℝ) : 0 ≤ growthWeight ρ x :=
  (by norm_num : (0 : ℝ) ≤ 1).trans (growthWeight_ge_one ρ x)

lemma growthFactor_pos (ρ : ℕ) : 0 < growthFactor ρ := by
  unfold growthFactor
  positivity

lemma continuous_growthWeight (ρ : ℕ) : Continuous (growthWeight ρ) := by
  unfold growthWeight
  fun_prop

lemma growthWeight_sub (ρ : ℕ) (x y : ℝ) :
    growthWeight ρ (x - y) ≤ growthFactor ρ * (growthWeight ρ x + growthWeight ρ y) := by
  have habs := abs_sub x y
  have hp : |x - y| ^ ρ ≤ (2 : ℝ) ^ (ρ - 1) * (|x| ^ ρ + |y| ^ ρ) :=
    (pow_le_pow_left₀ (abs_nonneg _) habs ρ).trans (add_pow_le (abs_nonneg x) (abs_nonneg y) ρ)
  have hw : |x| ^ ρ + |y| ^ ρ ≤ growthWeight ρ x + growthWeight ρ y := by
    unfold growthWeight
    linarith [abs_nonneg x, abs_nonneg y]
  have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ (2 : ℝ) ^ (ρ - 1) by positivity)
  have hl : 1 + |x - y| ≤ growthWeight ρ x + growthWeight ρ y := by
    unfold growthWeight
    linarith [pow_nonneg (abs_nonneg x) ρ, pow_nonneg (abs_nonneg y) ρ]
  unfold growthWeight at hl hm ⊢
  unfold growthFactor
  nlinarith

lemma growthWeight_le_three {ρ : ℕ} {x : ℝ} (hx : |x| ≤ 1) : growthWeight ρ x ≤ 3 := by
  have hp : |x| ^ ρ ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg x) hx ρ
  unfold growthWeight
  linarith

lemma growthWeight_local_bound (ρ : ℕ) (x₀ : ℝ) {x : ℝ} (hx : |x - x₀| ≤ 1) :
    growthWeight ρ x ≤ growthFactor ρ * (growthWeight ρ x₀ + 3) := by
  have h := growthWeight_sub ρ x₀ (x₀ - x)
  have hg : growthWeight ρ (x₀ - x) ≤ 3 :=
    growthWeight_le_three (by simpa only [abs_sub_comm] using hx)
  have hm := mul_le_mul_of_nonneg_left (add_le_add (le_refl (growthWeight ρ x₀)) hg)
    (growthFactor_pos ρ).le
  have he : x₀ - (x₀ - x) = x := by ring
  rw [he] at h
  exact h.trans hm

end ChenProof


open MeasureTheory Filter
open scoped Topology

namespace ChenProof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integrable_growthWeight [IsFiniteMeasure μ] {ρ : ℕ} {W : Ω → ℝ}
    (hW : Integrable W μ) (hpow : Integrable (fun ω => |W ω| ^ ρ) μ) :
    Integrable (fun ω => growthWeight ρ (W ω)) μ := by
  exact ((integrable_const 1).add hW.abs).add hpow

lemma integrable_translate [IsFiniteMeasure μ] {ρ : ℕ} {W : Ω → ℝ}
    (hW : AEStronglyMeasurable W μ)
    (hw : Integrable (fun ω => growthWeight ρ (W ω)) μ)
    {V : ℝ → ℝ} (hV : Continuous V) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ x, |V x| ≤ A * growthWeight ρ x) (x : ℝ) :
    Integrable (fun ω => V (x - W ω)) μ := by
  have hdom : Integrable (fun ω => A * growthFactor ρ *
      (growthWeight ρ x + growthWeight ρ (W ω))) μ :=
    ((integrable_const _).add hw).const_mul _
  refine hdom.mono' (hV.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub hW)) ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  exact (hb _).trans (by
    have hh := mul_le_mul_of_nonneg_left (growthWeight_sub ρ x (W ω)) hA
    simpa only [mul_assoc] using hh)

lemma continuous_integral_translate [IsFiniteMeasure μ] {ρ : ℕ} {W : Ω → ℝ}
    (hW : AEStronglyMeasurable W μ)
    (hw : Integrable (fun ω => growthWeight ρ (W ω)) μ)
    {V : ℝ → ℝ} (hV : Continuous V) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ x, |V x| ≤ A * growthWeight ρ x) :
    Continuous (fun x => ∫ ω, V (x - W ω) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let B := growthFactor ρ * (growthWeight ρ x₀ + 3)
  have hdom : Integrable (fun ω => A * growthFactor ρ * (B + growthWeight ρ (W ω))) μ :=
    ((integrable_const _).add hw).const_mul _
  apply continuousAt_of_dominated (bound := fun ω => A * growthFactor ρ * (B + growthWeight ρ (W ω)))
  · exact Filter.Eventually.of_forall fun x =>
      hV.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub hW)
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    have hxb : growthWeight ρ x ≤ B := growthWeight_local_bound ρ x₀
      (by simpa only [Metric.mem_ball, Real.dist_eq] using hx.le)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    calc
      |V (x - W ω)| ≤ A * growthWeight ρ (x - W ω) := hb _
      _ ≤ A * (growthFactor ρ * (growthWeight ρ x + growthWeight ρ (W ω))) :=
        mul_le_mul_of_nonneg_left (growthWeight_sub ρ x (W ω)) hA
      _ ≤ A * (growthFactor ρ * (B + growthWeight ρ (W ω))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add hxb (le_refl _)) (growthFactor_pos ρ).le) hA
      _ = A * growthFactor ρ * (B + growthWeight ρ (W ω)) := by ring
  · exact hdom
  · exact Filter.Eventually.of_forall fun ω => (hV.comp (continuous_id.sub continuous_const)).continuousAt

lemma integral_translate_growth [IsProbabilityMeasure μ] {ρ : ℕ} {W : Ω → ℝ}
    (hW : AEStronglyMeasurable W μ)
    (hw : Integrable (fun ω => growthWeight ρ (W ω)) μ)
    {V : ℝ → ℝ} (hV : Continuous V) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ x, |V x| ≤ A * growthWeight ρ x) :
    ∃ B ≥ 0, ∀ x, |∫ ω, V (x - W ω) ∂μ| ≤ B * growthWeight ρ x := by
  let I : ℝ := ∫ ω, growthWeight ρ (W ω) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun ω => growthWeight_nonneg ρ (W ω)
  let K := A * growthFactor ρ
  have hK : 0 ≤ K := mul_nonneg hA (growthFactor_pos ρ).le
  refine ⟨K * (1 + I), mul_nonneg hK (by linarith), fun x => ?_⟩
  have hi := integrable_translate hW hw hV hA hb x
  have hdom : Integrable (fun ω => K * (growthWeight ρ x + growthWeight ρ (W ω))) μ :=
    ((integrable_const _).add hw).const_mul _
  calc
    |∫ ω, V (x - W ω) ∂μ| ≤ ∫ ω, |V (x - W ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, K * (growthWeight ρ x + growthWeight ρ (W ω)) ∂μ :=
      integral_mono hi.abs hdom fun ω => (hb _).trans (by
        have hh := mul_le_mul_of_nonneg_left (growthWeight_sub ρ x (W ω)) hA
        simpa only [K, mul_assoc] using hh)
    _ = K * (growthWeight ρ x + I) := by
      rw [integral_const_mul, integral_add (integrable_const _) hw]
      simp [I]
    _ ≤ K * (1 + I) * growthWeight ρ x := by
      have hh := growthWeight_ge_one ρ x
      have hmul := mul_le_mul_of_nonneg_left hh hI
      nlinarith

end ChenProof


namespace ChenProof

def HasGrowth (ρ : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ A ≥ 0, ∀ x, |f x| ≤ A * growthWeight ρ x

lemma hasGrowth_const (ρ : ℕ) (b : ℝ) : HasGrowth ρ (fun _ => b) := by
  refine ⟨|b|, abs_nonneg b, fun x => ?_⟩
  have h := mul_le_mul_of_nonneg_left (growthWeight_ge_one ρ x) (abs_nonneg b)
  simpa only [mul_one] using h

lemma hasGrowth_linear (ρ : ℕ) (c : ℝ) : HasGrowth ρ (fun x => c * x) := by
  refine ⟨|c|, abs_nonneg c, fun x => ?_⟩
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  unfold growthWeight
  linarith [pow_nonneg (abs_nonneg x) ρ]

lemma HasGrowth.add {ρ : ℕ} {f g : ℝ → ℝ} (hf : HasGrowth ρ f) (hg : HasGrowth ρ g) :
    HasGrowth ρ (fun x => f x + g x) := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, fun x => ?_⟩
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ A * growthWeight ρ x + B * growthWeight ρ x := add_le_add (hf x) (hg x)
    _ = _ := by ring

lemma HasGrowth.neg {ρ : ℕ} {f : ℝ → ℝ} (hf : HasGrowth ρ f) :
    HasGrowth ρ (fun x => -f x) := by
  obtain ⟨A, hA, hf⟩ := hf
  exact ⟨A, hA, fun x => by simpa only [abs_neg] using hf x⟩

lemma HasGrowth.sub {ρ : ℕ} {f g : ℝ → ℝ} (hf : HasGrowth ρ f) (hg : HasGrowth ρ g) :
    HasGrowth ρ (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma HasGrowth.shift {ρ : ℕ} {f : ℝ → ℝ} (hf : HasGrowth ρ f) (d : ℝ) :
    HasGrowth ρ (fun x => f (x - d)) := by
  obtain ⟨A, hA, hf⟩ := hf
  let B := A * growthFactor ρ
  have hB : 0 ≤ B := mul_nonneg hA (growthFactor_pos ρ).le
  refine ⟨B * (1 + growthWeight ρ d), mul_nonneg hB (by linarith [growthWeight_nonneg ρ d]), fun x => ?_⟩
  have hwd := growthWeight_nonneg ρ d
  have hmul := mul_le_mul_of_nonneg_left (growthWeight_ge_one ρ x) hwd
  calc
    |f (x - d)| ≤ A * growthWeight ρ (x - d) := hf _
    _ ≤ B * (growthWeight ρ x + growthWeight ρ d) := by
      simpa only [B, mul_assoc] using
        mul_le_mul_of_nonneg_left (growthWeight_sub ρ x d) hA
    _ ≤ B * (1 + growthWeight ρ d) * growthWeight ρ x := by nlinarith

lemma HasGrowth.threshold {ρ : ℕ} {f : ℝ → ℝ} (hf : HasGrowth ρ f) (s b : ℝ) :
    HasGrowth ρ (fun x => if x < s then b else f x) := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨|b| + A, add_nonneg (abs_nonneg b) hA, fun x => ?_⟩
  have hw := growthWeight_nonneg ρ x
  dsimp only
  split_ifs
  · have h := mul_le_mul_of_nonneg_left (growthWeight_ge_one ρ x) (abs_nonneg b)
    nlinarith
  · have h := hf x
    have hmul := mul_nonneg (abs_nonneg b) hw
    nlinarith

end ChenProof


open MeasureTheory

namespace ChenProof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma convex_expected_translate {W : Ω → ℝ} {h : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ h)
    (hi : ∀ x, Integrable (fun ω => h (x - W ω)) μ) :
    ConvexOn ℝ Set.univ (fun x => ∫ ω, h (x - W ω) ∂μ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have he (ω : Ω) : a * x + b * y - W ω = a * (x - W ω) + b * (y - W ω) := by
    nlinarith [congrArg (· * W ω) hab]
  have hp (ω : Ω) : h (a * x + b * y - W ω) ≤ a * h (x - W ω) + b * h (y - W ω) := by
    rw [he]
    exact hc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hh := integral_mono (hi (a * x + b * y)) (((hi x).const_mul a).add ((hi y).const_mul b)) hp
  simpa only [Pi.add_def, Pi.sub_def, integral_add ((hi x).const_mul a) ((hi y).const_mul b), integral_const_mul,
    smul_eq_mul] using hh

omit [IsProbabilityMeasure μ] in
lemma continuous_expected_convex {W : Ω → ℝ} {h : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ h)
    (hi : ∀ x, Integrable (fun ω => h (x - W ω)) μ) :
    Continuous (fun x => ∫ ω, h (x - W ω) ∂μ) := by
  exact continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ (convex_expected_translate hc hi))

lemma kconvex_expected_translate {W : Ω → ℝ} {f : ℝ → ℝ} {k : ℝ}
    (hf : BertsekasKConvex k f)
    (hi : ∀ x, Integrable (fun ω => f (x - W ω)) μ) :
    BertsekasKConvex k (fun x => ∫ ω, f (x - W ω) ∂μ) := by
  intro z b y hz hb
  have hp (ω : Ω) : f (y - W ω) + (z / b) * (f (y - W ω) - f (y - b - W ω)) ≤
      k + f (z + y - W ω) := by
    have h₁ : (y - W ω) - b = y - b - W ω := by ring
    have h₂ : z + (y - W ω) = z + y - W ω := by ring
    simpa only [h₁, h₂] using hf z b (y - W ω) hz hb
  have hs : Integrable (fun ω => f (y - W ω) - f (y - b - W ω)) μ :=
    (hi y).sub (hi (y - b))
  have hc : Integrable (fun ω => (z / b) * (f (y - W ω) - f (y - b - W ω))) μ :=
    hs.const_mul (z / b)
  have hh := integral_mono ((hi y).add hc) ((integrable_const k).add (hi (z + y))) hp
  simp only [Pi.add_def] at hh
  rw [integral_add (hi y) hc, integral_const_mul, integral_sub (hi y) (hi (y - b)),
    integral_add (integrable_const k) (hi (z + y))] at hh
  simpa only [integral_const, probReal_univ, one_smul] using hh

end ChenProof


namespace ChenProof

lemma continuous_compact_max {R ψ : ℝ → ℝ} {lo hi c : ℝ}
    (hR : ContinuousOn R (Set.Icc lo hi)) (hψ : Continuous ψ) :
    Continuous (fun y : ℝ => sSup ((fun d => R d - c * y + ψ (y - d)) '' Set.Icc lo hi)) := by
  let D := Set.Icc lo hi
  let : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_Icc
  have hrestrict : Continuous (fun d : D => R d) := hR.domRestrict
  have hh : Continuous (fun z : ℝ × D => R z.2 - c * z.1 + ψ (z.1 - z.2)) := by
    exact ((hrestrict.comp continuous_snd).sub (continuous_const.mul continuous_fst)).add
      (hψ.comp (continuous_fst.sub (continuous_subtype_val.comp continuous_snd)))
  have hmax := (isCompact_univ : IsCompact (Set.univ : Set D)).continuous_sSup
    (f := fun y (d : D) => R d - c * y + ψ (y - d)) hh
  have he (y : ℝ) : (fun d : D => R d - c * y + ψ (y - d)) '' Set.univ =
      (fun d => R d - c * y + ψ (y - d)) '' Set.Icc lo hi := by
    ext z
    constructor
    · rintro ⟨d, _, rfl⟩
      exact ⟨d, d.property, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, Set.mem_univ _, rfl⟩
  simpa only [he] using hmax

lemma compact_maximum_attained {R ψ : ℝ → ℝ} {lo hi c : ℝ}
    (hlo : lo ≤ hi) (hR : ContinuousOn R (Set.Icc lo hi)) (hψ : Continuous ψ) (y : ℝ) :
    ∃ d ∈ Set.Icc lo hi,
      sSup ((fun d => R d - c * y + ψ (y - d)) '' Set.Icc lo hi) = R d - c * y + ψ (y - d) ∧
      ∀ e ∈ Set.Icc lo hi, R e - c * y + ψ (y - e) ≤
        sSup ((fun d => R d - c * y + ψ (y - d)) '' Set.Icc lo hi) := by
  have hc : ContinuousOn (fun d => R d - c * y + ψ (y - d)) (Set.Icc lo hi) :=
    (hR.sub continuousOn_const).add (hψ.comp (continuous_const.sub continuous_id)).continuousOn
  obtain ⟨d, hd, he, hmax⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge
    (Set.nonempty_Icc.mpr hlo) hc
  exact ⟨d, hd, he, fun e he' => by rw [he]; exact hmax e he'⟩

end ChenProof


namespace ChenProof

def OrderedKConvex (k : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y l : ℝ, x ≤ y → 0 ≤ l → l ≤ 1 →
    f ((1-l)*x+l*y) ≤ (1-l)*f x+l*f y+l*k

theorem ordered_of_bertsekas {k : ℝ} {f : ℝ → ℝ}
    (hk : 0 ≤ k) (hf : BertsekasKConvex k f) : OrderedKConvex k f := by
  intro x y l hxy hl hl1
  by_cases h0 : l = 0
  · subst l
    simp
  by_cases h1 : l = 1
  · subst l
    simp only [sub_self, zero_mul, one_mul, zero_add]
    linarith
  by_cases he : x = y
  · subst y
    have hp : (1-l)*x+l*x=x := by ring
    rw [hp]
    nlinarith
  have hlp : 0 < l := lt_of_le_of_ne hl (Ne.symm h0)
  have hlt : l < 1 := lt_of_le_of_ne hl1 h1
  have hxp : x < y := lt_of_le_of_ne hxy he
  have hb : 0 < l*(y-x) := mul_pos hlp (sub_pos.mpr hxp)
  have hz : 0 ≤ (1-l)*(y-x) := mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hxy)
  have h := hf ((1-l)*(y-x)) (l*(y-x)) ((1-l)*x+l*y) hz hb
  have he₀ : (1-l)*x+l*y-l*(y-x)=x := by ring
  have he₁ : (1-l)*(y-x)+((1-l)*x+l*y)=y := by ring
  rw [he₀, he₁] at h
  have hq : l * (((1-l)*(y-x))/(l*(y-x))) = 1-l := by
    field_simp [hlp.ne', (sub_pos.mpr hxp).ne']
  have hm := mul_le_mul_of_nonneg_left h hl
  rw [mul_add, ← mul_assoc, hq] at hm
  nlinarith

theorem bertsekas_of_ordered {k : ℝ} {f : ℝ → ℝ}
    (hf : OrderedKConvex k f) : BertsekasKConvex k f := by
  intro z b y hz hb
  have hden : 0 < b+z := by linarith
  have hl : 0 ≤ b/(b+z) := div_nonneg hb.le hden.le
  have hl1 : b/(b+z) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have h := hf (y-b) (z+y) (b/(b+z)) (by linarith) hl hl1
  have he : (1-b/(b+z))*(y-b)+(b/(b+z))*(z+y)=y := by
    field_simp [hden.ne']
    ring
  rw [he] at h
  have hq : (b+z)*(b/(b+z))=b  := by field_simp [hden.ne']
  have hq' : (b+z)*(1-b/(b+z))=z := by rw [mul_sub, mul_one, hq]; ring
  have hm := mul_le_mul_of_nonneg_left h hden.le
  simp only [mul_add, ← mul_assoc, hq, hq'] at hm
  have hratio : b*(z/b)=z := by field_simp
  have hh : b*(f y+(z/b)*(f y-f (y-b))) ≤ b*(k+f (z+y)) := by
    rw [mul_add, ← mul_assoc, hratio]
    nlinarith
  exact (mul_le_mul_iff_right₀ hb).mp hh

theorem bertsekas_iff_ordered {k : ℝ} {f : ℝ → ℝ} (hk : 0 ≤ k) :
    BertsekasKConvex k f ↔ OrderedKConvex k f :=
  ⟨ordered_of_bertsekas hk, bertsekas_of_ordered⟩

end ChenProof


open Filter Set
open scoped Topology
namespace ChenProof

theorem exists_threshold {k : ℝ} {f : ℝ → ℝ} (hk : 0 ≤ k)
    (hc : Continuous f) (hf : BertsekasKConvex k f)
    (hbot : Tendsto f atBot atTop) (htop : Tendsto f atTop atTop) :
    ∃ s S : ℝ, s ≤ S ∧ (∀ y, f S ≤ f y) ∧ f s = f S + k ∧
      (∀ x, x < s → f S + k < f x) ∧
      (∀ x y, s ≤ x → x ≤ y → f x ≤ f y + k) := by
  have hlim : Tendsto f (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact hbot.sup htop
  obtain ⟨S, hS⟩ := hc.exists_forall_le hlim
  let L := f S + k
  let A : Set ℝ := {x | f x ≤ L}
  have hne : A.Nonempty := ⟨S, by dsimp [A, L]; linarith⟩
  obtain ⟨a, ha⟩ := (eventually_atBot.1 (hbot.eventually (eventually_gt_atTop L)))
  obtain ⟨b, hb⟩ := (eventually_atTop.1 (htop.eventually (eventually_gt_atTop L)))
  have hclosed : IsClosed A := isClosed_le hc continuous_const
  have hcompact : IsCompact A := (isCompact_Icc : IsCompact (Icc a b)).of_isClosed_subset hclosed (by
    intro x hx
    change f x ≤ L at hx
    constructor
    · by_contra h
      have := ha x (le_of_lt (lt_of_not_ge h))
      linarith
    · by_contra h
      have := hb x (le_of_lt (lt_of_not_ge h))
      linarith)
  obtain ⟨s, hs, hleast⟩ := hcompact.exists_isLeast hne
  have hsS : s ≤ S := hleast (by dsimp [A, L]; linarith)
  have hsval : f s = L := by
    apply le_antisymm hs
    by_contra h
    have hlt : f s < L := lt_of_not_ge h
    have hev : ∀ᶠ x in 𝓝 s, f x < L := hc.continuousAt.eventually (gt_mem_nhds hlt)
    obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
    have hd : dist (s-ε/2) s < ε := by
      rw [Real.dist_eq, show s-ε/2-s = -(ε/2) by ring, abs_neg,
        abs_of_pos (half_pos hε)]
      linarith
    have hm : s-ε/2 ∈ A := (he hd).le
    have := hleast hm
    linarith
  have hleft : ∀ x, x < s → L < f x := by
    intro x hx
    by_contra hn
    have := hleast (show x ∈ A from le_of_not_gt hn)
    linarith
  have hmiddle : ∀ x, s ≤ x → x ≤ S → f x ≤ L := by
    intro x hsx hxS
    by_cases he : x = s
    · simpa [he] using hsval.le
    have hxs : 0 < x-s := sub_pos.mpr (lt_of_le_of_ne hsx (Ne.symm he))
    have hh := hf (S-x) (x-s) x (sub_nonneg.mpr hxS) hxs
    rw [show S-x+x=S by ring, show x-(x-s)=s by ring, hsval] at hh
    have hq : 0 ≤ (S-x)/(x-s) := div_nonneg (sub_nonneg.mpr hxS) hxs.le
    dsimp [L] at *
    nlinarith
  refine ⟨s, S, hsS, hS, hsval, hleft, ?_⟩
  intro x y hsx hxy
  by_cases hxS : x ≤ S
  · have hm := hmiddle x hsx hxS
    have hy := hS y
    dsimp [L] at hm
    linarith
  · have hSx : 0 < x-S := sub_pos.mpr (lt_of_not_ge hxS)
    have hh := hf (y-x) (x-S) x (sub_nonneg.mpr hxy) hSx
    rw [show y-x+x=y by ring, show x-(x-S)=S by ring] at hh
    have hq : 0 ≤ (y-x)/(x-S) := div_nonneg (sub_nonneg.mpr hxy) hSx.le
    have hm := hS x
    nlinarith

end ChenProof


noncomputable section
namespace ChenProof

def costClip (s L : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := if s ≤ x then f x else L

theorem costClip_continuous {s L : ℝ} {f : ℝ → ℝ}
    (hc : Continuous f) (hs : f s = L) : Continuous (costClip s L f) := by
  exact hc.if_le continuous_const continuous_const continuous_id (fun x hx => by
    change s = x at hx
    simpa [← hx] using hs)

theorem costClip_kconvex {k s L : ℝ} {f : ℝ → ℝ}
    (hk : 0 ≤ k) (hf : BertsekasKConvex k f) (hs : f s = L)
    (hmin : ∀ y, L ≤ f y + k) : BertsekasKConvex k (costClip s L f) := by
  apply bertsekas_of_ordered
  have hford := ordered_of_bertsekas hk hf
  intro x y l hxy hl hl1
  let z := (1-l)*x+l*y
  have hxz : x ≤ z := by dsimp [z]; nlinarith
  have hzy : z ≤ y := by dsimp [z]; nlinarith
  change costClip s L f z ≤ (1-l)*costClip s L f x+l*costClip s L f y+l*k
  by_cases hsx : s ≤ x
  · have hsy := hsx.trans hxy
    have hsz := hsx.trans hxz
    simpa only [costClip, if_pos hsx, if_pos hsy, if_pos hsz] using hford x y l hxy hl hl1
  have hxs : x < s := lt_of_not_ge hsx
  by_cases hsy : s ≤ y
  · simp only [costClip, if_neg hsx, if_pos hsy]
    by_cases hsz : s ≤ z
    · rw [if_pos hsz]
      by_cases hys : y = s
      · have hzs : z = s := le_antisymm (hys ▸ hzy) hsz
        rw [hzs, hys, hs]
        nlinarith
      have hden : 0 < y-s := sub_pos.mpr (lt_of_le_of_ne hsy (Ne.symm hys))
      let θ := (z-s)/(y-s)
      have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hsz) hden.le
      have hθ1 : θ ≤ 1 := (div_le_one hden).mpr (by linarith)
      have hθl : θ ≤ l := (div_le_iff₀ hden).mpr (by dsimp [z]; nlinarith)
      have he : (1-θ)*s+θ*y=z := by
        dsimp [θ]
        field_simp [hden.ne']
        ring
      have hh := hford s y θ hsy hθ hθ1
      rw [he, hs] at hh
      have hm := mul_le_mul_of_nonneg_right hθl (sub_nonneg.mpr (hmin y))
      nlinarith
    · rw [if_neg hsz]
      have hm := mul_nonneg hl (sub_nonneg.mpr (hmin y))
      nlinarith
  · have hsz : ¬s ≤ z := by intro h; exact hsy (h.trans hzy)
    simp only [costClip, if_neg hsx, if_neg hsy, if_neg hsz]
    nlinarith

end ChenProof


noncomputable section
open Filter Set
open ChenSimchiLevi.Additive
namespace ChenProof

def rewardObj (k : ℝ) (G : ℝ → ℝ) (x y : ℝ) : ℝ := -k * delta (y-x) + G y

def orderReward (k : ℝ) (G : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((rewardObj k G x) '' Ici x)

theorem exists_reward_envelope {k : ℝ} {G : ℝ → ℝ} (hk : 0 ≤ k)
    (hc : Continuous G) (hG : BertsekasKConvex k (fun x => -G x))
    (hbot : Tendsto G atBot atBot) (htop : Tendsto G atTop atBot) :
    ∃ s S : ℝ, s ≤ S ∧ (∀ y, G y ≤ G S) ∧ G s = G S-k ∧
      (∀ x, orderReward k G x = if x < s then G S-k else G x) ∧
      Continuous (orderReward k G) ∧ BertsekasKConvex k (fun x => -orderReward k G x) ∧
      (∀ x, x ≤ sSOrder s S x ∧
        (∀ y, x ≤ y → rewardObj k G x y ≤ rewardObj k G x (sSOrder s S x)) ∧
        orderReward k G x = rewardObj k G x (sSOrder s S x)) := by
  obtain ⟨s, S, hsS, hS, hs, hleft, hright⟩ := exists_threshold hk hc.neg hG
    (tendsto_neg_atBot_atTop.comp hbot) (tendsto_neg_atBot_atTop.comp htop)
  simp only [Pi.neg_apply] at hS hs hleft hright
  have hmax : ∀ y, G y ≤ G S := by intro y; have := hS y; linarith
  have hval : G s = G S-k := by linarith
  have hopt (x : ℝ) : x ≤ sSOrder s S x ∧
      (∀ y, x ≤ y → rewardObj k G x y ≤ rewardObj k G x (sSOrder s S x)) := by
    by_cases hxs : x < s
    · have hxS : x < S := hxs.trans_le hsS
      simp only [sSOrder, if_pos hxs]
      refine ⟨hxS.le, ?_⟩
      intro y hxy
      have hSx : 0 < S-x := sub_pos.mpr hxS
      simp only [rewardObj, delta, if_pos hSx]
      by_cases hyx : x < y
      · rw [if_pos (sub_pos.mpr hyx)]
        have := hmax y
        linarith
      · have hy : y=x := le_antisymm (le_of_not_gt hyx) hxy
        subst y
        have := hleft x hxs
        simp only [sub_self, lt_self_iff_false, if_false, mul_zero, zero_add, mul_one]
        linarith
    · have hsx : s ≤ x := le_of_not_gt hxs
      simp only [sSOrder, if_neg hxs]
      refine ⟨le_rfl, ?_⟩
      intro y hxy
      simp only [rewardObj, delta, sub_self, lt_self_iff_false, if_false, mul_zero, zero_add]
      by_cases hyx : x < y
      · rw [if_pos (sub_pos.mpr hyx)]
        have := hright x y hsx hxy
        linarith
      · have hy : y=x := le_antisymm (le_of_not_gt hyx) hxy
        subst y
        simp
  have heq (x : ℝ) : orderReward k G x = rewardObj k G x (sSOrder s S x) := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨sSOrder s S x, (hopt x).1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hopt x).2 y hy
  have hdisplay (x : ℝ) : orderReward k G x = if x<s then G S-k else G x := by
    rw [heq]
    by_cases hxs : x<s
    · have hxS : 0 < S-x := sub_pos.mpr (hxs.trans_le hsS)
      simp only [sSOrder, if_pos hxs, rewardObj, delta, if_pos hxS]
      ring
    · simp [sSOrder, hxs, rewardObj, delta]
  have hclip : (fun x => -orderReward k G x) = costClip s (-G S+k) (fun x => -G x) := by
    funext x
    rw [hdisplay]
    by_cases hx : x<s
    · simp only [costClip, if_pos hx, if_neg (not_le.mpr hx)]
      ring
    · simp [costClip, hx, le_of_not_gt hx]
  have hcc := costClip_continuous hc.neg hs
  have hkc := costClip_kconvex hk hG hs (fun y => by have := hS y; linarith)
  have hcontneg : Continuous (fun x => -orderReward k G x) := by rw [hclip]; exact hcc
  have hcont : Continuous (orderReward k G) := by
    have hh := hcontneg.neg
    change Continuous (fun x => - -orderReward k G x) at hh
    simpa only [neg_neg] using hh
  refine ⟨s, S, hsS, hmax, hval, hdisplay, hcont, ?_, ?_⟩
  · rw [hclip]
    exact hkc
  · intro x
    exact ⟨(hopt x).1, (hopt x).2, heq x⟩

end ChenProof


namespace ChenProof

theorem concave_inward_sum {lo hi : ℝ} {R : ℝ → ℝ}
    (hR : ConcaveOn ℝ (Set.Icc lo hi) R) {a b u v : ℝ}
    (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hau : a ≤ u) (hub : u ≤ b) (hsum : u+v=a+b) :
    R a+R b ≤ R u+R v := by
  by_cases hab : a=b
  · have hua : u=a := by linarith
    have hva : v=a := by linarith
    simp [hab, hua, hva]
  have hd : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne (hau.trans hub) hab)
  let t := (u-a)/(b-a)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hau) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have he₁ : (1-t)*a+t*b=u := by
    dsimp [t]
    field_simp [hd.ne']
    ring
  have he₂ : t*a+(1-t)*b=v := by
    have : (t*a+(1-t)*b)+((1-t)*a+t*b)=a+b := by ring
    rw [he₁] at this
    linarith
  have h₁ := hR.2 ha hb (sub_nonneg.mpr ht1) ht (by ring : (1-t)+t=1)
  have h₂ := hR.2 ha hb ht (sub_nonneg.mpr ht1) (by ring : t+(1-t)=1)
  simp only [smul_eq_mul, he₁, he₂] at h₁ h₂
  nlinarith

def stageObj (R ψ : ℝ → ℝ) (c y d : ℝ) : ℝ := R d-c*y+ψ (y-d)

theorem ordered_maximizers {lo hi c : ℝ} {R ψ H : ℝ → ℝ}
    (hR : ConcaveOn ℝ (Set.Icc lo hi) R)
    (hupper : ∀ y d, d ∈ Set.Icc lo hi → stageObj R ψ c y d ≤ H y)
    (hatt : ∀ y, ∃ d ∈ Set.Icc lo hi, H y = stageObj R ψ c y d)
    {y₀ y₁ : ℝ} (hy : y₀ ≤ y₁) :
    ∃ d₀ ∈ Set.Icc lo hi, ∃ d₁ ∈ Set.Icc lo hi,
      H y₀ = stageObj R ψ c y₀ d₀ ∧ H y₁ = stageObj R ψ c y₁ d₁ ∧ y₀-d₀ ≤ y₁-d₁ := by
  obtain ⟨d₀, hd₀, he₀⟩ := hatt y₀
  obtain ⟨d₁, hd₁, he₁⟩ := hatt y₁
  by_cases hord : y₀-d₀ ≤ y₁-d₁
  · exact ⟨d₀, hd₀, d₁, hd₁, he₀, he₁, hord⟩
  have hrev : y₁-d₁ < y₀-d₀ := lt_of_not_ge hord
  let e₀ := y₀-(y₁-d₁)
  let e₁ := y₁-(y₀-d₀)
  have hb₀ : d₀ ≤ e₀ ∧ e₀ ≤ d₁ := by dsimp [e₀]; constructor <;> linarith
  have hb₁ : d₀ ≤ e₁ ∧ e₁ ≤ d₁ := by dsimp [e₁]; constructor <;> linarith
  have hem₀ : e₀ ∈ Set.Icc lo hi := ⟨hd₀.1.trans hb₀.1, hb₀.2.trans hd₁.2⟩
  have hem₁ : e₁ ∈ Set.Icc lo hi := ⟨hd₀.1.trans hb₁.1, hb₁.2.trans hd₁.2⟩
  have hesum : e₀+e₁=d₀+d₁ := by dsimp [e₀,e₁]; ring
  have hsum := concave_inward_sum hR hd₀ hd₁ hb₀.1 hb₀.2 hesum
  have hu₀ := hupper y₀ e₀ hem₀
  have hu₁ := hupper y₁ e₁ hem₁
  have hn₀ : y₀-e₀=y₁-d₁ := by dsimp [e₀]; ring
  have hn₁ : y₁-e₁=y₀-d₀ := by dsimp [e₁]; ring
  have hsobj : stageObj R ψ c y₀ d₀ + stageObj R ψ c y₁ d₁ ≤
      stageObj R ψ c y₀ e₀ + stageObj R ψ c y₁ e₁ := by
    simp only [stageObj, hn₀, hn₁]
    linarith
  refine ⟨e₀, hem₀, e₁, hem₁, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · rw [hn₀, hn₁]
    exact hrev.le

end ChenProof


namespace ChenProof

theorem maximized_kconvex {lo hi c k : ℝ} {R ψ H : ℝ → ℝ}
    (hk : 0 ≤ k) (hψ : BertsekasKConvex k (fun x => -ψ x))
    (hR : ConcaveOn ℝ (Set.Icc lo hi) R)
    (hupper : ∀ y d, d ∈ Set.Icc lo hi → stageObj R ψ c y d ≤ H y)
    (hatt : ∀ y, ∃ d ∈ Set.Icc lo hi, H y = stageObj R ψ c y d) :
    BertsekasKConvex k (fun y => -H y) := by
  apply bertsekas_of_ordered
  intro y₀ y₁ l hy hl hl1
  obtain ⟨d₀, hd₀, d₁, hd₁, he₀, he₁, hn⟩ := ordered_maximizers hR hupper hatt hy
  have h1l : 0 ≤ 1-l := sub_nonneg.mpr hl1
  have hdm : (1-l)*d₀+l*d₁ ∈ Set.Icc lo hi := by
    constructor
    · nlinarith [mul_nonneg h1l (sub_nonneg.mpr hd₀.1),
        mul_nonneg hl (sub_nonneg.mpr hd₁.1)]
    · nlinarith [mul_nonneg h1l (sub_nonneg.mpr hd₀.2),
        mul_nonneg hl (sub_nonneg.mpr hd₁.2)]
  have hcontinuation := ordered_of_bertsekas hk hψ (y₀-d₀) (y₁-d₁) l hn hl hl1
  have hrev := hR.2 hd₀ hd₁ h1l hl (by ring : (1-l)+l=1)
  simp only [smul_eq_mul] at hrev
  have hu := hupper ((1-l)*y₀+l*y₁) ((1-l)*d₀+l*d₁) hdm
  have he : ((1-l)*y₀+l*y₁)-((1-l)*d₀+l*d₁) =
      (1-l)*(y₀-d₀)+l*(y₁-d₁) := by ring
  simp only [stageObj, he] at hu
  simp only [stageObj] at he₀ he₁
  dsimp only at hcontinuation ⊢
  nlinarith

end ChenProof


namespace ChenProof

lemma kconvex_add_linear {k : ℝ} {f : ℝ → ℝ}
    (hf : BertsekasKConvex k f) (a b : ℝ) :
    BertsekasKConvex k (fun x => f x + a*x+b) := by
  intro z t y hz ht
  have hh := hf z t y hz ht
  have hcancel : (z/t)*t=z := div_mul_cancel₀ z ht.ne'
  dsimp only
  calc
    (f y+a*y+b)+(z/t)*((f y+a*y+b)-(f (y-t)+a*(y-t)+b)) =
        f y+(z/t)*(f y-f (y-t))+a*(z+y)+b := by
      nlinarith [congrArg (fun q : ℝ => a*q) hcancel]
    _ ≤ k+(f (z+y)+a*(z+y)+b) := by linarith

lemma kconvex_linear_add {k : ℝ} {f : ℝ → ℝ}
    (hf : BertsekasKConvex k f) (a b : ℝ) :
    BertsekasKConvex k (fun x => a*x+b+f x) := by
  have he : (fun x => a*x+b+f x) = (fun x => f x+a*x+b) := by
    funext x
    ring
  rw [he]
  exact kconvex_add_linear hf a b

lemma convex_kconvex_zero {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    BertsekasKConvex 0 f := by
  apply bertsekas_of_ordered
  intro x y l _ hl hl1
  have hh := hf.2 (Set.mem_univ x) (Set.mem_univ y)
    (sub_nonneg.mpr hl1) hl (by ring : (1-l)+l=1)
  simpa only [smul_eq_mul, mul_zero, add_zero] using hh

lemma kconvex_add {k j : ℝ} {f g : ℝ → ℝ}
    (hf : BertsekasKConvex k f) (hg : BertsekasKConvex j g) :
    BertsekasKConvex (k+j) (fun x => f x+g x) := by
  intro z b y hz hb
  have hhf := hf z b y hz hb
  have hhg := hg z b y hz hb
  dsimp only
  nlinarith

lemma convex_add_kconvex {k : ℝ} {f g : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : BertsekasKConvex k g) :
    BertsekasKConvex k (fun x => f x+g x) := by
  simpa only [zero_add] using kconvex_add (convex_kconvex_zero hf) hg

end ChenProof


open Filter Set
namespace ChenProof

lemma uniform_shift_atTop {f : ℝ → ℝ} (hf : Tendsto f atTop atTop)
    (lo hi d₀ B : ℝ) :
    ∀ᶠ y in atTop, ∀ d ∈ Icc lo hi, B ≤ f (y-d+d₀) := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hf.eventually (eventually_ge_atTop B))
  filter_upwards [eventually_ge_atTop (a+hi-d₀)] with y hy
  intro d hd
  exact ha (y-d+d₀) (by linarith [hd.2])

lemma uniform_shift_atBot {f : ℝ → ℝ} (hf : Tendsto f atBot atTop)
    (lo hi d₀ B : ℝ) :
    ∀ᶠ y in atBot, ∀ d ∈ Icc lo hi, B ≤ f (y-d+d₀) := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp (hf.eventually (eventually_ge_atTop B))
  filter_upwards [eventually_le_atBot (a+lo-d₀)] with y hy
  intro d hd
  exact ha (y-d+d₀) (by linarith [hd.1])

end ChenProof


open MeasureTheory
open ChenSimchiLevi.Additive

namespace ChenProof

noncomputable def holdMean (M : Model) (t : ℕ) (z : ℝ) : ℝ :=
  ∫ ε : ℝ × ℝ, M.h t (z - ε.2) ∂(M.μ t)

noncomputable def continuationPsi (M : Model) (V : ℝ → ℝ) (t : ℕ) (z : ℝ) : ℝ :=
  -holdMean M t z + ∫ ε : ℝ × ℝ, V (z - ε.2) ∂(M.μ t)

lemma beta_weight_integrable {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) :
    Integrable (fun ε : ℝ × ℝ => growthWeight M.ρ ε.2) (M.μ t) := by
  let : IsProbabilityMeasure (M.μ t) := hA.prob t ht
  let d := M.dlo t
  have hd : d ∈ Set.Icc (M.dlo t) (M.dhi t) := ⟨le_rfl, hA.dlo_le_dhi t ht⟩
  have hW : Integrable (fun ε : ℝ × ℝ => d + ε.2) (M.μ t) :=
    (integrable_const d).add (hA.beta_integrable t ht)
  have hp : Integrable (fun ε : ℝ × ℝ => |d + ε.2| ^ M.ρ) (M.μ t) := by
    apply (hA.moment t ht d hd).congr
    filter_upwards [hadd t ht] with ε hε
    simp only [hε, one_mul]
  have hw := integrable_growthWeight hW hp
  have hdom := (hw.add (integrable_const (growthWeight M.ρ d))).const_mul (growthFactor M.ρ)
  refine hdom.mono' ((continuous_growthWeight M.ρ).comp_aestronglyMeasurable
    (hA.beta_integrable t ht).aestronglyMeasurable) ?_
  filter_upwards [] with ε
  rw [Real.norm_eq_abs, abs_of_nonneg (growthWeight_nonneg _ _)]
  simpa only [add_sub_cancel_left, Pi.add_def] using growthWeight_sub M.ρ (d + ε.2) d

lemma holding_integrable {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) (z : ℝ) :
    Integrable (fun ε : ℝ × ℝ => M.h t (z - ε.2)) (M.μ t) := by
  have hd : M.dlo t ∈ Set.Icc (M.dlo t) (M.dhi t) := ⟨le_rfl, hA.dlo_le_dhi t ht⟩
  apply (hA.h_integrable t ht (z + M.dlo t) (M.dlo t) hd).congr
  filter_upwards [hadd t ht] with ε hε
  simp only [hε, one_mul]
  congr 1
  ring

lemma G_eq_holdMean {M : Model} (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) (y d : ℝ) :
    M.G t y d = holdMean M t (y - d) := by
  apply integral_congr_ae
  filter_upwards [hadd t ht] with ε hε
  simp only [hε, one_mul]
  congr 1
  ring

lemma continuous_holdMean {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) : Continuous (holdMean M t) := by
  let : IsProbabilityMeasure (M.μ t) := hA.prob t ht
  exact continuous_expected_convex (hA.h_convex t ht) (holding_integrable hA hadd ht)

lemma continuation_integrable {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ} (hV : Continuous V)
    {A : ℝ} (hA0 : 0 ≤ A) (hb : ∀ x, |V x| ≤ A * growthWeight M.ρ x) (z : ℝ) :
    Integrable (fun ε : ℝ × ℝ => V (z - ε.2)) (M.μ t) := by
  let : IsProbabilityMeasure (M.μ t) := hA.prob t ht
  exact integrable_translate (hA.beta_integrable t ht).aestronglyMeasurable
    (beta_weight_integrable hA hadd ht) hV hA0 hb z

lemma continuous_continuationPsi {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ} (hV : Continuous V)
    {A : ℝ} (hA0 : 0 ≤ A) (hb : ∀ x, |V x| ≤ A * growthWeight M.ρ x) :
    Continuous (continuationPsi M V t) := by
  let : IsProbabilityMeasure (M.μ t) := hA.prob t ht
  exact (continuous_holdMean hA hadd ht).neg.add
    (continuous_integral_translate (hA.beta_integrable t ht).aestronglyMeasurable
      (beta_weight_integrable hA hadd ht) hV hA0 hb)

lemma gWith_eq_stage {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ} (hV : Continuous V)
    {A : ℝ} (hA0 : 0 ≤ A) (hb : ∀ x, |V x| ≤ A * growthWeight M.ρ x)
    (y d : ℝ) :
    M.gWith V t y d = M.R t d - M.c t * y + continuationPsi M V t (y - d) := by
  have hh := holding_integrable hA hadd ht (y - d)
  have hv := continuation_integrable hA hadd ht hV hA0 hb (y - d)
  unfold Model.gWith continuationPsi holdMean
  congr 1
  calc
    _ = ∫ ε : ℝ × ℝ, -M.h t (y - d - ε.2) + V (y - d - ε.2) ∂(M.μ t) := by
      apply integral_congr_ae
      filter_upwards [hadd t ht] with ε hε
      simp only [hε, one_mul]
      have he : y - (d + ε.2) = y - d - ε.2 := by ring
      rw [he]
    _ = _ := by
      have hn : Integrable (fun ε : ℝ × ℝ => -M.h t (y - d - ε.2)) (M.μ t) := hh.neg
      rw [integral_add hn hv, integral_neg]

end ChenProof


open MeasureTheory
open ChenSimchiLevi.Additive
namespace ChenProof

lemma hasGrowth_G {M : Model} (hA : M.Assumptions) {t : ℕ}
    (ht : t ∈ Finset.Icc 1 M.T) {d : ℝ} (hd : d ∈ Set.Icc (M.dlo t) (M.dhi t)) :
    HasGrowth M.ρ (fun y => M.G t y d) := by
  obtain ⟨C, hC⟩ := hA.G_growth t ht
  refine ⟨|C|, abs_nonneg C, fun y => ?_⟩
  rw [abs_of_nonneg (hA.G_nonneg t ht y d hd)]
  calc
    M.G t y d ≤ C * (1 + |y| ^ M.ρ) := hC y d hd
    _ ≤ |C| * (1 + |y| ^ M.ρ) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * growthWeight M.ρ y := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
      unfold growthWeight
      linarith [abs_nonneg y]

lemma hasGrowth_holdMean {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) : HasGrowth M.ρ (holdMean M t) := by
  have hg := (hasGrowth_G hA ht ⟨le_rfl, hA.dlo_le_dhi t ht⟩).shift (-M.dlo t)
  convert hg using 1
  ext z
  rw [G_eq_holdMean hadd ht]
  congr 1
  ring

lemma hasGrowth_continuationPsi {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) : HasGrowth M.ρ (continuationPsi M V t) := by
  let : IsProbabilityMeasure (M.μ t) := hA.prob t ht
  obtain ⟨A, hA0, hb⟩ := hVG
  have he : HasGrowth M.ρ (fun z => ∫ ε : ℝ × ℝ, V (z - ε.2) ∂(M.μ t)) :=
    integral_translate_growth (hA.beta_integrable t ht).aestronglyMeasurable
      (beta_weight_integrable hA hadd ht) hV hA0 hb
  exact (hasGrowth_holdMean hA hadd ht).neg.add he

lemma uniform_stage_growth {ρ : ℕ} {R ψ : ℝ → ℝ} {lo hi c : ℝ}
    (hR : ContinuousOn R (Set.Icc lo hi)) (hψ : HasGrowth ρ ψ) :
    ∃ A ≥ 0, ∀ y d, d ∈ Set.Icc lo hi →
      |R d - c * y + ψ (y - d)| ≤ A * growthWeight ρ y := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_growthWeight ρ).continuousOn
  obtain ⟨A, hA, hψ⟩ := hψ
  let L := A * growthFactor ρ * (1 + |D|)
  have hAK : 0 ≤ A * growthFactor ρ := mul_nonneg hA (growthFactor_pos ρ).le
  have hL : 0 ≤ L := mul_nonneg hAK (by positivity)
  refine ⟨|B| + |c| + L, by positivity, fun y d hd => ?_⟩
  have hrd0 : |R d| ≤ B := by simpa only [Real.norm_eq_abs] using hB d hd
  have hrd : |R d| ≤ |B| := hrd0.trans (le_abs_self B)
  have hwd : growthWeight ρ d ≤ |D| := by
    have hh := hD d hd
    rw [Real.norm_eq_abs, abs_of_nonneg (growthWeight_nonneg ρ d)] at hh
    exact hh.trans (le_abs_self D)
  have hwy := growthWeight_ge_one ρ y
  have hyy : |y| ≤ growthWeight ρ y := by
    unfold growthWeight
    linarith [pow_nonneg (abs_nonneg y) ρ]
  have hpd : |ψ (y-d)| ≤ L * growthWeight ρ y := by
    have h1 := growthWeight_sub ρ y d
    have h2 := mul_le_mul_of_nonneg_left h1 hA
    have h3 := mul_le_mul_of_nonneg_left hwy (abs_nonneg D)
    have h4 := hψ (y-d)
    have hi : growthWeight ρ y + growthWeight ρ d ≤ (1 + |D|) * growthWeight ρ y := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hi hAK
    calc
      _ ≤ A * (growthFactor ρ * (growthWeight ρ y + growthWeight ρ d)) := h4.trans h2
      _ ≤ L * growthWeight ρ y := by simpa only [L, mul_assoc] using hm
  calc
    |R d - c*y + ψ (y-d)| ≤ |R d| + |c*y| + |ψ (y-d)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ |B| * growthWeight ρ y + |c| * growthWeight ρ y + L * growthWeight ρ y := by
      rw [abs_mul]
      exact add_le_add (add_le_add (hrd.trans (by nlinarith [abs_nonneg B]))
        (mul_le_mul_of_nonneg_left hyy (abs_nonneg c))) hpd
    _ = _ := by ring

end ChenProof


open MeasureTheory
open ChenSimchiLevi.Additive
namespace ChenProof

lemma kconvex_continuationPsi {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V)
    (hk : BertsekasKConvex M.k (fun x => -V x)) :
    BertsekasKConvex M.k (fun z => -continuationPsi M V t z) := by
  let : IsProbabilityMeasure (M.μ t) := hA.prob t ht
  obtain ⟨A, hA0, hb⟩ := hVG
  have hf := convex_add_kconvex (hA.h_convex t ht) hk
  have hi (z : ℝ) : Integrable (fun ε : ℝ × ℝ => M.h t (z-ε.2) + -V (z-ε.2)) (M.μ t) :=
    (holding_integrable hA hadd ht z).add (continuation_integrable hA hadd ht hV hA0 hb z).neg
  have he (z : ℝ) : (∫ ε : ℝ × ℝ, M.h t (z-ε.2) + -V (z-ε.2) ∂(M.μ t)) =
      -continuationPsi M V t z := by
    have hn : Integrable (fun ε : ℝ × ℝ => -V (z-ε.2)) (M.μ t) :=
      (continuation_integrable hA hadd ht hV hA0 hb z).neg
    rw [integral_add (holding_integrable hA hadd ht z) hn, integral_neg]
    unfold continuationPsi holdMean
    ring
  simpa only [he] using kconvex_expected_translate hf hi

end ChenProof


open ChenSimchiLevi.Additive
namespace ChenProof

lemma continuous_revenue {M : Model} (hA : M.Assumptions) {t : ℕ}
    (ht : t ∈ Finset.Icc 1 M.T) : ContinuousOn (M.R t) (Set.Icc (M.dlo t) (M.dhi t)) :=
  continuousOn_id.mul (hA.P_continuous t ht)

lemma native_maximum_attained {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) (y : ℝ) :
    ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t), M.GstarWith V t y = M.gWith V t y d ∧
      ∀ e ∈ Set.Icc (M.dlo t) (M.dhi t), M.gWith V t y e ≤ M.GstarWith V t y := by
  obtain ⟨A,hA0,hb⟩ := hVG
  have he := gWith_eq_stage hA hadd ht hV hA0 hb
  simpa only [Model.GstarWith, he] using compact_maximum_attained
    (hA.dlo_le_dhi t ht) (continuous_revenue hA ht)
    (continuous_continuationPsi hA hadd ht hV hA0 hb) y

lemma continuous_native_maximum {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) : Continuous (M.GstarWith V t) := by
  obtain ⟨A,hA0,hb⟩ := hVG
  have he := gWith_eq_stage hA hadd ht hV hA0 hb
  change Continuous (fun y => M.GstarWith V t y)
  simpa only [Model.GstarWith, he] using
    (continuous_compact_max (c := M.c t) (continuous_revenue hA ht)
      (continuous_continuationPsi hA hadd ht hV hA0 hb))

lemma growth_native_maximum {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) : HasGrowth M.ρ (M.GstarWith V t) := by
  obtain ⟨A,hA0,hb⟩ := uniform_stage_growth (c := M.c t) (continuous_revenue hA ht)
    (hasGrowth_continuationPsi hA hadd ht hV hVG)
  obtain ⟨B,hB0,hVB⟩ := hVG
  refine ⟨A,hA0,fun y => ?_⟩
  obtain ⟨d,hd,he,_⟩ := native_maximum_attained hA hadd ht hV ⟨B,hB0,hVB⟩ y
  rw [he, gWith_eq_stage hA hadd ht hV hB0 hVB]
  exact hb y d hd

lemma kconvex_native_maximum {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V)
    (hk : BertsekasKConvex M.k (fun x => -V x)) :
    BertsekasKConvex M.k (fun y => -M.GstarWith V t y) := by
  apply maximized_kconvex hA.k_nonneg (kconvex_continuationPsi hA hadd ht hV hVG hk)
    (hA.R_concave t ht)
  · intro y d hd
    obtain ⟨A,hA0,hb⟩ := hVG
    obtain ⟨e,he,_,hu⟩ := native_maximum_attained hA hadd ht hV ⟨A,hA0,hb⟩ y
    simpa only [stageObj, gWith_eq_stage hA hadd ht hV hA0 hb] using hu d hd
  · intro y
    obtain ⟨A,hA0,hb⟩ := hVG
    obtain ⟨d,hd,he,_⟩ := native_maximum_attained hA hadd ht hV ⟨A,hA0,hb⟩ y
    exact ⟨d,hd,by simpa only [stageObj, gWith_eq_stage hA hadd ht hV hA0 hb] using he⟩

end ChenProof


open MeasureTheory
open ChenSimchiLevi.Additive
namespace ChenProof

lemma integral_continuation_affine_le {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) {c B : ℝ}
    (hbound : ∀ x, V x ≤ c*x+B) (z : ℝ) :
    (∫ ε : ℝ × ℝ, V (z-ε.2) ∂(M.μ t)) ≤ c*z+B := by
  let : IsProbabilityMeasure (M.μ t) := hA.prob t ht
  obtain ⟨A,hA0,hb⟩ := hVG
  have hz : Integrable (fun ε : ℝ × ℝ => z-ε.2) (M.μ t) :=
    (integrable_const z).sub (hA.beta_integrable t ht)
  have hc : Integrable (fun ε : ℝ × ℝ => c*(z-ε.2)) (M.μ t) := hz.const_mul c
  have hh := integral_mono (continuation_integrable hA hadd ht hV hA0 hb z)
    (hc.add (integrable_const B)) (fun ε => hbound (z-ε.2))
  simp only [Pi.add_def] at hh
  rw [integral_add hc (integrable_const B), integral_const_mul,
    integral_sub (integrable_const z) (hA.beta_integrable t ht)] at hh
  simpa only [integral_const, probReal_univ, one_smul, hA.beta_mean t ht, sub_zero] using hh

lemma stage_affine_le {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) {B : ℝ}
    (hbound : ∀ x, V x ≤ M.c (t+1)*x+B) (y d : ℝ) :
    M.gWith V t y d ≤ M.R t d -(M.c t-M.c (t+1))*y - M.G t y d - M.c (t+1)*d+B := by
  obtain ⟨A,hA0,hb⟩ := hVG
  rw [gWith_eq_stage hA hadd ht hV hA0 hb, G_eq_holdMean hadd ht]
  unfold continuationPsi
  have hh := integral_continuation_affine_le hA hadd ht hV ⟨A,hA0,hb⟩ hbound (y-d)
  linarith

lemma G_shift_reference {M : Model} (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) (y d d₀ : ℝ) :
    M.G t y d = M.G t (y-d+d₀) d₀ := by
  rw [G_eq_holdMean hadd ht, G_eq_holdMean hadd ht]
  congr 1
  ring

end ChenProof


open Filter
open ChenSimchiLevi.Additive
namespace ChenProof

lemma native_maximum_atTop {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) {B : ℝ}
    (hbound : ∀ x, V x ≤ M.c (t+1)*x+B) :
    Tendsto (M.GstarWith V t) atTop atBot := by
  let q := M.c t-M.c (t+1)
  let F := fun z => q*z+M.G t z (M.dlo t)
  let C := fun d => M.R t d-M.c (t+1)*d-q*(d-M.dlo t)+B
  have hc : ContinuousOn C (Set.Icc (M.dlo t) (M.dhi t)) := by
    exact (((continuous_revenue hA ht).sub (continuous_const.mul continuous_id).continuousOn).sub
      (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn).add continuousOn_const
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hF : Tendsto F atTop atTop := hA.G_atTop t ht (M.dlo t) ⟨le_rfl,hA.dlo_le_dhi t ht⟩
  apply tendsto_atBot.2
  intro b
  filter_upwards [uniform_shift_atTop hF (M.dlo t) (M.dhi t) (M.dlo t) (K-b)] with y hy
  obtain ⟨d,hd,he,_⟩ := native_maximum_attained hA hadd ht hV hVG y
  have hstage := stage_affine_le hA hadd ht hV hVG hbound y d
  have hconst : C d ≤ K := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK d hd)
  have hf := hy d hd
  rw [G_shift_reference hadd ht y d (M.dlo t)] at hstage
  rw [he]
  dsimp [F,C,q] at hf hconst
  linarith

lemma native_maximum_atBot {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : Continuous V) (hVG : HasGrowth M.ρ V) {B : ℝ}
    (hbound : ∀ x, V x ≤ M.c (t+1)*x+B) (hcn : 0 ≤ M.c (t+1)) :
    Tendsto (M.GstarWith V t) atBot atBot := by
  let F := fun z => M.c t*z+M.G t z (M.dlo t)
  let C := fun d => M.R t d-M.c (t+1)*d-M.c t*(d-M.dlo t)+B
  have hc : ContinuousOn C (Set.Icc (M.dlo t) (M.dhi t)) := by
    exact (((continuous_revenue hA ht).sub (continuous_const.mul continuous_id).continuousOn).sub
      (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn).add continuousOn_const
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hF : Tendsto F atBot atTop := hA.G_atBot t ht (M.dlo t) ⟨le_rfl,hA.dlo_le_dhi t ht⟩
  apply tendsto_atBot.2
  intro b
  filter_upwards [uniform_shift_atBot hF (M.dlo t) (M.dhi t) (M.dlo t) (K-b),
    eventually_le_atBot (0 : ℝ)] with y hy hy0
  obtain ⟨d,hd,he,_⟩ := native_maximum_attained hA hadd ht hV hVG y
  have hstage := stage_affine_le hA hadd ht hV hVG hbound y d
  have hconst : C d ≤ K := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK d hd)
  have hf := hy d hd
  have hneg := mul_nonpos_of_nonneg_of_nonpos hcn hy0
  rw [G_shift_reference hadd ht y d (M.dlo t)] at hstage
  rw [he]
  dsimp [F,C] at hf hconst
  nlinarith

end ChenProof


open ChenSimchiLevi.Additive
namespace ChenProof

def ValueRegular (M : Model) (c : ℝ) (V : ℝ → ℝ) : Prop :=
  Continuous V ∧ HasGrowth M.ρ V ∧ BertsekasKConvex M.k (fun x => -V x) ∧
    ∃ B, ∀ x, V x ≤ c*x+B

noncomputable def stageValue (M : Model) (V : ℝ → ℝ) (t : ℕ) (x : ℝ) : ℝ :=
  M.c t*x + orderReward M.k (M.GstarWith V t) x

lemma stage_regular {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : ValueRegular M (M.c (t+1)) V) (hcn : 0 ≤ M.c (t+1)) :
    ValueRegular M (M.c t) (stageValue M V t) := by
  obtain ⟨hc,hgrowth,hk,B,hB⟩ := hV
  have hG := kconvex_native_maximum hA hadd ht hc hgrowth hk
  obtain ⟨s,S,_,hmax,_,hdisplay,hcont,hkenv,_⟩ := exists_reward_envelope hA.k_nonneg
    (continuous_native_maximum hA hadd ht hc hgrowth) hG
    (native_maximum_atBot hA hadd ht hc hgrowth hB hcn)
    (native_maximum_atTop hA hadd ht hc hgrowth hB)
  have henvgrowth : HasGrowth M.ρ (orderReward M.k (M.GstarWith V t)) := by
    have hh := (growth_native_maximum hA hadd ht hc hgrowth).threshold s
      (M.GstarWith V t S-M.k)
    simpa only [← hdisplay] using hh
  refine ⟨(continuous_const.mul continuous_id).add hcont,
    (hasGrowth_linear M.ρ (M.c t)).add henvgrowth, ?_, M.GstarWith V t S, ?_⟩
  · have hh := kconvex_linear_add hkenv (-M.c t) 0
    convert hh using 1
    funext x
    unfold stageValue
    ring
  · intro x
    unfold stageValue
    rw [hdisplay]
    split_ifs
    · linarith [hA.k_nonneg]
    · linarith [hmax x]

lemma stage_policy {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) {V : ℝ → ℝ}
    (hV : ValueRegular M (M.c (t+1)) V) (hcn : 0 ≤ M.c (t+1)) :
    ∃ s S : ℝ, s ≤ S ∧ ∀ x,
      x ≤ sSOrder s S x ∧
      (∀ y, x ≤ y → M.orderObjWith V t x y ≤ M.orderObjWith V t x (sSOrder s S x)) ∧
      stageValue M V t x = M.c t*x + M.orderObjWith V t x (sSOrder s S x) := by
  obtain ⟨hc,hgrowth,hk,B,hB⟩ := hV
  obtain ⟨s,S,hsS,_,_,_,_,_,hop⟩ := exists_reward_envelope hA.k_nonneg
    (continuous_native_maximum hA hadd ht hc hgrowth)
    (kconvex_native_maximum hA hadd ht hc hgrowth hk)
    (native_maximum_atBot hA hadd ht hc hgrowth hB hcn)
    (native_maximum_atTop hA hadd ht hc hgrowth hB)
  refine ⟨s,S,hsS,fun x => ?_⟩
  obtain ⟨hfeas,hopt,he⟩ := hop x
  exact ⟨hfeas,hopt,congrArg (fun z => M.c t*x+z) he⟩

end ChenProof


open ChenSimchiLevi.Additive
namespace ChenProof

lemma next_cost_nonneg {M : Model} (hA : M.Assumptions) {t : ℕ}
    (ht : t ∈ Finset.Icc 1 M.T) : 0 ≤ M.c (t+1) := by
  have htt := Finset.mem_Icc.mp ht
  by_cases he : t=M.T
  · rw [he,hA.c_terminal]
  · exact hA.c_nonneg (t+1) (Finset.mem_Icc.mpr (by omega))

lemma vAux_regular {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive) :
    ∀ n, n ≤ M.T → ValueRegular M (M.c (M.T+1-n)) (M.vAux n) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨continuous_const,hasGrowth_const M.ρ 0,?_,0,?_⟩
    · intro z b y _ _
      simp only [Model.vAux,neg_zero,sub_self,mul_zero,add_zero]
      exact hA.k_nonneg
    · intro x
      simp only [Nat.sub_zero,hA.c_terminal,Model.vAux,zero_mul,add_zero,le_refl]
  | succ n ih =>
    intro hn
    have ht : M.T-n ∈ Finset.Icc 1 M.T := Finset.mem_Icc.mpr (by omega)
    have he : M.T+1-n=(M.T-n)+1 := by omega
    have hv := ih (by omega)
    rw [he] at hv
    have hs := stage_regular hA hadd ht hv (next_cost_nonneg hA ht)
    have hi : M.T+1-(n+1)=M.T-n := by omega
    rw [hi]
    exact hs

lemma continuation_regular {M : Model} (hA : M.Assumptions) (hadd : M.IsAdditive)
    {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) :
    ValueRegular M (M.c (t+1)) (M.v (t+1)) := by
  have htt := Finset.mem_Icc.mp ht
  have hn : M.T+1-(t+1) ≤ M.T := by omega
  have hi : M.T+1-(M.T+1-(t+1))=t+1 := by omega
  have hh := vAux_regular hA hadd (M.T+1-(t+1)) hn
  rw [hi] at hh
  exact hh

lemma value_stage_eq {M : Model} {t : ℕ} (ht : t ∈ Finset.Icc 1 M.T) :
    M.v t = stageValue M (M.v (t+1)) t := by
  have htt := Finset.mem_Icc.mp ht
  have hi : M.T+1-t=(M.T-t)+1 := by omega
  have hj : M.T+1-(t+1)=M.T-t := by omega
  have hl : M.T-(M.T-t)=t := by omega
  unfold Model.v
  rw [hi, Model.vAux, hl, hj]
  rfl

end ChenProof


open ChenProof

namespace ChenSimchiLevi.Additive

/-- Theorem 3.1(c)–(d) of Chen–Simchi-Levi (2004), p. 890: under additive demand, for every period
`t = T, …, 1`,
(c) `g_t(·, d)` attains its maximum over `[d_t, d̄_t]` at every `y`, and `g_t(y, d_t(y))` and
`v_t(x)` are `k`-concave;
(d) there are `s_t ≤ S_t` such that the `(s, S)` order — order up to `S_t` if `x < s_t`, otherwise
do not order — attains the maximum in (2), `v_t(x)` equals `c_t x` plus that maximum, and the
expected demand is set to a maximizer of `g_t(y, ·)` at the post-order level `y`. -/
theorem native_recovery (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive) :
    ∀ t ∈ Finset.Icc 1 M.T,
      ((∀ y : ℝ, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d) ∧
        BertsekasKConvex M.k (fun y => -M.Gstar t y) ∧
        BertsekasKConvex M.k (fun x => -M.v t x)) ∧
      (∃ s S : ℝ, s ≤ S ∧ ∀ x : ℝ,
        x ≤ sSOrder s S x ∧
        (∀ y : ℝ, x ≤ y → M.orderObj t x y ≤ M.orderObj t x (sSOrder s S x)) ∧
        M.v t x = M.c t * x + M.orderObj t x (sSOrder s S x) ∧
        ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t (sSOrder s S x)) (Set.Icc (M.dlo t) (M.dhi t)) d) := by
  intro t ht
  have hv := continuation_regular hA hadd ht
  have hcn := next_cost_nonneg hA ht
  have hc := hv.1
  have hg := hv.2.1
  have hk := hv.2.2.1
  have hatt (y : ℝ) : ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
      IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d := by
    obtain ⟨d,hd,he,hu⟩ := native_maximum_attained hA hadd ht hc hg y
    refine ⟨d,hd,fun e he' => ?_⟩
    have hh := hu e he'
    rw [he] at hh
    exact hh
  have hG := kconvex_native_maximum hA hadd ht hc hg hk
  have hval := (stage_regular hA hadd ht hv hcn).2.2.1
  rw [← value_stage_eq ht] at hval
  refine ⟨⟨hatt,hG,hval⟩,?_⟩
  obtain ⟨s,S,hsS,hpolicy⟩ := stage_policy hA hadd ht hv hcn
  refine ⟨s,S,hsS,fun x => ?_⟩
  obtain ⟨hf,ho,he⟩ := hpolicy x
  rw [← value_stage_eq ht] at he
  exact ⟨hf,ho,he,hatt _⟩

end ChenSimchiLevi.Additive


namespace ChenSimchiLevi.Additive

/-- Theorem 3.1(c)–(d) of Chen–Simchi-Levi (2004), p. 890: under additive demand, for every period
`t = T, …, 1`,
(c) `g_t(·, d)` attains its maximum over `[d_t, d̄_t]` at every `y`, and `g_t(y, d_t(y))` and
`v_t(x)` are `k`-concave;
(d) there are `s_t ≤ S_t` such that the `(s, S)` order — order up to `S_t` if `x < s_t`, otherwise
do not order — attains the maximum in (2), `v_t(x)` equals `c_t x` plus that maximum, and the
expected demand is set to a maximizer of `g_t(y, ·)` at the post-order level `y`. -/
theorem theorem_3_1 (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive) :
    ∀ t ∈ Finset.Icc 1 M.T,
      ((∀ y : ℝ, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d) ∧
        BertsekasKConvex M.k (fun y => -M.Gstar t y) ∧
        BertsekasKConvex M.k (fun x => -M.v t x)) ∧
      (∃ s S : ℝ, s ≤ S ∧ ∀ x : ℝ,
        x ≤ sSOrder s S x ∧
        (∀ y : ℝ, x ≤ y → M.orderObj t x y ≤ M.orderObj t x (sSOrder s S x)) ∧
        M.v t x = M.c t * x + M.orderObj t x (sSOrder s S x) ∧
        ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t (sSOrder s S x)) (Set.Icc (M.dlo t) (M.dhi t)) d) := by
  exact native_recovery M hA hadd

end ChenSimchiLevi.Additive

open ChenSimchiLevi.Additive

theorem solution (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive) :
    ∀ t ∈ Finset.Icc 1 M.T,
      ((∀ y : ℝ, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d) ∧
        BertsekasKConvex M.k (fun y => -M.Gstar t y) ∧
        BertsekasKConvex M.k (fun x => -M.v t x)) ∧
      (∃ s S : ℝ, s ≤ S ∧ ∀ x : ℝ,
        x ≤ sSOrder s S x ∧
        (∀ y : ℝ, x ≤ y → M.orderObj t x y ≤ M.orderObj t x (sSOrder s S x)) ∧
        M.v t x = M.c t * x + M.orderObj t x (sSOrder s S x) ∧
        ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
          IsMaxOn (M.g t (sSOrder s S x)) (Set.Icc (M.dlo t) (M.dhi t)) d) := ChenSimchiLevi.Additive.theorem_3_1 M hA hadd
