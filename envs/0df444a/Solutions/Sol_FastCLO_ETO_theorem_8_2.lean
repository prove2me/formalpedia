-- Prove2me | solution 2 for FastCLO.ETO.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:56:04.962449+00:00
-- url     : https://prove2.me/submissions/f36d21a1-caed-4912-afa1-0ac2caa241df

import Mathlib
import Definitions.Def_FastCLO_ETO_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace RRAux_FCLO

open FastCLO.ETO Filter Topology

lemma ext_finite {d : ℕ} (P : Polytope d) : P.ext.Finite := by
  classical
  let act : FastCLO.ERM.Vec d → Finset (Fin P.m) :=
    fun z => Finset.univ.filter (fun i => ⟪P.A i, z⟫_ℝ = P.b i)
  apply Set.Finite.of_finite_image (f := act) (Set.toFinite _)
  intro z hz z' hz' heq
  by_contra hne
  have hzZ : z ∈ P.Z := hz.1
  have hz'Z : z' ∈ P.Z := hz'.1
  have hact : ∀ i, ⟪P.A i, z⟫_ℝ = P.b i → ⟪P.A i, z - z'⟫_ℝ = 0 := by
    intro i hi
    have h1 : i ∈ act z := by simp [act, hi]
    rw [heq] at h1
    have h2 : ⟪P.A i, z'⟫_ℝ = P.b i := by simpa [act] using h1
    rw [inner_sub_right, hi, h2, sub_self]
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, ⟪P.A i, z + t • (z - z')⟫_ℝ ≤ P.b i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : ⟪P.A i, z⟫_ℝ = P.b i
    · refine Filter.Eventually.of_forall (fun t => ?_)
      rw [inner_add_right, inner_smul_right, hact i hi]
      simp [hi]
    · have hlt : ⟪P.A i, z⟫_ℝ < P.b i := lt_of_le_of_ne (hzZ i) hi
      have hc : Continuous (fun t : ℝ => ⟪P.A i, z + t • (z - z')⟫_ℝ) := by fun_prop
      have h0 : (fun t : ℝ => ⟪P.A i, z + t • (z - z')⟫_ℝ) 0 < P.b i := by simpa using hlt
      exact (hc.continuousAt.eventually (gt_mem_nhds h0)).mono (fun t ht => ht.le)
  obtain ⟨t, ht, ht01⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num))).exists
  have h1 : z + t • (z - z') ∈ P.Z := ht
  have h2 : z - t • (z - z') ∈ P.Z := by
    intro i
    have e : z - t • (z - z') = (1 - t) • z + t • z' := by module
    rw [e, inner_add_right, inner_smul_right, inner_smul_right]
    have := hzZ i; have := hz'Z i
    nlinarith [ht01.1, ht01.2]
  have hmid : z ∈ openSegment ℝ (z - t • (z - z')) (z + t • (z - z')) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
  have hv : t • (z - z') = 0 := sub_eq_self.1 (hz.2 h2 h1 hmid)
  rcases smul_eq_zero.1 hv with h | h
  · linarith [ht01.1]
  · exact hne (sub_eq_zero.1 h)

lemma bdd_img {d : ℕ} (P : Polytope d) (F : FastCLO.ERM.Vec d) :
    BddBelow ((fun z => ⟪F, z⟫_ℝ) '' P.Z) := by
  refine ⟨-(‖F‖ * P.B), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have h1 := abs_real_inner_le_norm F z
  have h2 := P.bounded z hz
  have h3 : ‖F‖ * ‖z‖ ≤ ‖F‖ * P.B := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  simp only
  linarith [neg_abs_le ⟪F, z⟫_ℝ]

variable {p d : ℕ}

lemma ex_nonneg (P : Polytope d) (I : Instance p d) (x : FastCLO.ERM.Vec p)
    (π : FastCLO.ERM.Vec d) (hπ : π ∈ P.Z) : 0 ≤ ⟪I.fstar x, π⟫_ℝ - optVal P I x := by
  have := csInf_le (bdd_img P (I.fstar x)) ⟨π, hπ, rfl⟩
  unfold optVal; linarith

lemma ex_le (P : Polytope d) (I : Instance p d) (x : FastCLO.ERM.Vec p)
    (G π : FastCLO.ERM.Vec d) (hπ : π ∈ P.Z) (hmin : ∀ z ∈ P.Z, ⟪G, π⟫_ℝ ≤ ⟪G, z⟫_ℝ) :
    ⟪I.fstar x, π⟫_ℝ - optVal P I x ≤ 2 * P.B * ‖G - I.fstar x‖ := by
  have hne : ((fun z => ⟪I.fstar x, z⟫_ℝ) '' P.Z).Nonempty := P.nonempty.image _
  have : ⟪I.fstar x, π⟫_ℝ - 2 * P.B * ‖G - I.fstar x‖ ≤ optVal P I x := by
    apply le_csInf hne
    rintro _ ⟨z, hz, rfl⟩
    have e : ⟪I.fstar x, π⟫_ℝ - ⟪I.fstar x, z⟫_ℝ =
        ⟪I.fstar x - G, π - z⟫_ℝ + (⟪G, π⟫_ℝ - ⟪G, z⟫_ℝ) := by
      simp only [inner_sub_left, inner_sub_right]; ring
    have h1 := real_inner_le_norm (I.fstar x - G) (π - z)
    have h2 : ‖π - z‖ ≤ 2 * P.B := by
      have := norm_sub_le π z
      linarith [P.bounded π hπ, P.bounded z hz]
    have h3 : ‖I.fstar x - G‖ * ‖π - z‖ ≤ ‖G - I.fstar x‖ * (2 * P.B) := by
      rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h4 := hmin z hz
    simp only
    nlinarith
  linarith

lemma gap_le (P : Polytope d) (I : Instance p d) (x : FastCLO.ERM.Vec p)
    (π : FastCLO.ERM.Vec d) (hπ : π ∈ P.ext) (hpos : 0 < ⟪I.fstar x, π⟫_ℝ - optVal P I x) :
    0 < gap P I x ∧ gap P I x ≤ ⟪I.fstar x, π⟫_ℝ - optVal P I x := by
  have hπZ : π ∈ P.Z := hπ.1
  have hnot : π ∉ Zstar P I x := by
    intro h
    have : ⟪I.fstar x, π⟫_ℝ ≤ optVal P I x :=
      le_csInf (P.nonempty.image _) (by rintro _ ⟨z, hz, rfl⟩; exact h.2 z hz)
    linarith
  have hZ : Zstar P I x ≠ P.Z := fun h => hnot (h ▸ hπZ)
  have hfin : (P.ext \ Zstar P I x).Finite := (ext_finite P).subset Set.sdiff_subset
  have hne : ((fun z => ⟪I.fstar x, z⟫_ℝ) '' (P.ext \ Zstar P I x)).Nonempty :=
    ⟨_, π, ⟨hπ, hnot⟩, rfl⟩
  have hfin' := hfin.image (fun z => ⟪I.fstar x, z⟫_ℝ)
  obtain ⟨e, ⟨he, hes⟩, hval⟩ := hne.csInf_mem hfin'
  have hle : sInf ((fun z => ⟪I.fstar x, z⟫_ℝ) '' (P.ext \ Zstar P I x)) ≤ ⟪I.fstar x, π⟫_ℝ :=
    csInf_le hfin'.bddBelow ⟨π, ⟨hπ, hnot⟩, rfl⟩
  unfold gap
  rw [if_neg hZ]
  refine ⟨?_, by linarith⟩
  have heZ : e ∈ P.Z := he.1
  have : ∃ z' ∈ P.Z, ⟪I.fstar x, z'⟫_ℝ < ⟪I.fstar x, e⟫_ℝ := by
    by_contra hcon
    push Not at hcon
    exact hes ⟨heZ, hcon⟩
  obtain ⟨z', hz', hlt⟩ := this
  have := csInf_le (bdd_img P (I.fstar x)) ⟨z', hz', rfl⟩
  simp only at hval
  unfold optVal at *
  linarith


noncomputable def wt (α C₁ C₂ : ℝ) (j : ℕ) : ℝ :=
  (2 * (2:ℝ) ^ α) ^ (j + 1) * C₁ * Real.exp (-(C₂ * 4 ^ j))

noncomputable def Cst (α γ C₁ C₂ : ℝ) : ℝ :=
  2 * (2 * γ) ^ α * (1 + ∑' j, wt α C₁ C₂ j)

lemma wt_nonneg (α C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (j : ℕ) : 0 ≤ wt α C₁ C₂ j := by
  unfold wt; positivity

lemma exp_neg_le (y : ℝ) (hy : 0 < y) (m : ℕ) : Real.exp (-y) ≤ m.factorial / y ^ m := by
  have h := Real.pow_div_factorial_le_exp y hy.le m
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  have h1 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos (-y)).le
  nlinarith

lemma wt_summable (α C₁ C₂ : ℝ) (hα : 0 ≤ α) (hC₁ : 0 ≤ C₁) (hC₂ : 0 < C₂) :
    Summable (wt α C₁ C₂) := by
  set m := ⌈α⌉₊ + 1 with hm
  have hρ : 2 * (2:ℝ) ^ α ≤ 2 ^ m := by
    have : (2:ℝ) ^ α ≤ 2 ^ (⌈α⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil α)
    rw [Real.rpow_natCast] at this
    rw [hm, pow_succ]; linarith
  set r := (2 * (2:ℝ) ^ α) / 4 ^ m with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by positivity)]
    calc _ ≤ (2:ℝ) ^ m := hρ
      _ < 4 ^ m := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  refine Summable.of_nonneg_of_le (fun j => wt_nonneg α C₁ C₂ hC₁ j) (fun j => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left
      (2 * (2:ℝ) ^ α * C₁ * m.factorial / C₂ ^ m))
  have he := exp_neg_le (C₂ * 4 ^ j) (by positivity) m
  have h4 : ((4:ℝ) ^ j) ^ m = ((4:ℝ) ^ m) ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
  calc wt α C₁ C₂ j ≤ (2 * (2:ℝ) ^ α) ^ (j + 1) * C₁ * (m.factorial / (C₂ * 4 ^ j) ^ m) := by
        unfold wt; exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = 2 * (2:ℝ) ^ α * C₁ * m.factorial / C₂ ^ m * r ^ j := by
        rw [hr, div_pow, mul_pow C₂ ((4:ℝ) ^ j) m, h4]
        field_simp
        ring

lemma num_total (B α γ C₁ C₂ a : ℝ) (hB : 0 < B) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (ha : 0 < a) :
    ENNReal.ofReal (2 * B * a ^ (-(1/2:ℝ))) *
        ENNReal.ofReal ((γ * (2 * B * a ^ (-(1/2:ℝ))) / B) ^ α) +
      ∑' j : ℕ, ENNReal.ofReal (2 * B * (2 ^ (j + 1) * a ^ (-(1/2:ℝ)))) *
        ENNReal.ofReal (C₁ * Real.exp (-C₂ * a * (2 ^ j * a ^ (-(1/2:ℝ))) ^ 2)) *
        ENNReal.ofReal ((γ * (2 * B * (2 ^ (j + 1) * a ^ (-(1/2:ℝ)))) / B) ^ α)
      = ENNReal.ofReal (Cst α γ C₁ C₂ * B * a ^ (-(1 + α) / 2)) := by
  set u := a ^ (-(1/2:ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ha _
  have hua : u ^ 2 * a = 1 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  have hu1 : u * u ^ α = a ^ (-(1 + α) / 2) := by
    rw [← Real.rpow_one_add' hu0.le (by linarith), hu, ← Real.rpow_mul ha.le]
    ring_nf
  set M := 2 * B * (2 * γ) ^ α * (u * u ^ α) with hM
  have hM0 : 0 ≤ M := by positivity
  have h0 : (2 * B * u) * (γ * (2 * B * u) / B) ^ α = M := by
    have : γ * (2 * B * u) / B = (2 * γ) * u := by field_simp
    rw [this, Real.mul_rpow (by positivity) hu0.le, hM]; ring
  have hj : ∀ j : ℕ, (2 * B * (2 ^ (j + 1) * u)) * (C₁ * Real.exp (-C₂ * a * (2 ^ j * u) ^ 2)) *
      ((γ * (2 * B * (2 ^ (j + 1) * u)) / B) ^ α) = M * wt α C₁ C₂ j := by
    intro j
    have e1 : γ * (2 * B * (2 ^ (j + 1) * u)) / B = (2 * γ) * ((2:ℝ) ^ (j + 1) * u) := by
      field_simp
    have e2 : -C₂ * a * (2 ^ j * u) ^ 2 = -(C₂ * 4 ^ j) := by
      have : ((2:ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [mul_pow, this]
      linear_combination (-(C₂ * 4 ^ j)) * hua
    rw [e1, e2, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hu0.le, ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2),
      hM, wt, mul_pow]
    ring
  have hsum := wt_summable α C₁ C₂ hα hC₁.le hC₂
  rw [← ENNReal.ofReal_mul (by positivity), h0]
  have : ∀ j : ℕ, ENNReal.ofReal (2 * B * (2 ^ (j + 1) * u)) *
        ENNReal.ofReal (C₁ * Real.exp (-C₂ * a * (2 ^ j * u) ^ 2)) *
        ENNReal.ofReal ((γ * (2 * B * (2 ^ (j + 1) * u)) / B) ^ α) =
      ENNReal.ofReal (M * wt α C₁ C₂ j) := by
    intro j
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hj]
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hM0 (wt_nonneg α C₁ C₂ hC₁.le j))
    (hsum.mul_left M), tsum_mul_left, ← ENNReal.ofReal_add hM0
    (mul_nonneg hM0 (tsum_nonneg (fun j => wt_nonneg α C₁ C₂ hC₁.le j)))]
  congr 1
  rw [hM, Cst, ← hu1]
  ring


section Core
open Classical

lemma Cst_nonneg (α γ C₁ C₂ : ℝ) (hγ : 0 ≤ γ) (hC₁ : 0 ≤ C₁) : 0 ≤ Cst α γ C₁ C₂ := by
  unfold Cst
  have : 0 ≤ ∑' j, wt α C₁ C₂ j := tsum_nonneg (fun j => wt_nonneg α C₁ C₂ hC₁ j)
  positivity

lemma ofReal_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf)]
  · rw [integral_undef hi]; simp

lemma decomp (B u ex s Δ : ℝ) (hB : 0 < B) (hu : 0 < u) (h0 : 0 ≤ ex) (h1 : ex ≤ 2 * B * s)
    (h2 : 0 < ex → 0 < Δ ∧ Δ ≤ ex) :
    ENNReal.ofReal ex ≤ (if 0 < Δ ∧ Δ ≤ 2 * B * u then ENNReal.ofReal (2 * B * u) else 0) +
      ∑' j : ℕ, (if (0 < Δ ∧ Δ ≤ 2 * B * (2 ^ (j + 1) * u)) ∧ 2 ^ j * u ≤ s
        then ENNReal.ofReal (2 * B * (2 ^ (j + 1) * u)) else 0) := by
  rcases h0.eq_or_lt with h | hpos
  · rw [← h]; simp
  obtain ⟨hΔ, hΔe⟩ := h2 hpos
  by_cases hs : s < u
  · have : ex ≤ 2 * B * u := by nlinarith
    rw [if_pos ⟨hΔ, by linarith⟩]
    exact le_add_right (ENNReal.ofReal_le_ofReal this)
  · push Not at hs
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near
      (show 1 ≤ s / u by rw [le_div_iff₀ hu]; linarith) (show (1:ℝ) < 2 by norm_num)
    rw [le_div_iff₀ hu] at hj1
    rw [div_lt_iff₀ hu] at hj2
    have hb : ex ≤ 2 * B * (2 ^ (j + 1) * u) := by nlinarith
    refine le_add_left (le_trans ?_ (ENNReal.le_tsum j))
    rw [if_pos ⟨⟨hΔ, by linarith⟩, by linarith⟩]
    exact ENNReal.ofReal_le_ofReal hb

lemma core {ΩD X : Type*} [MeasurableSpace ΩD] [MeasurableSpace X] (ν : Measure ΩD)
    (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (ex s : ΩD → X → ℝ) (Δ : X → ℝ) (hs : Measurable (Function.uncurry s))
    (B α γ C₁ C₂ a : ℝ) (hB : 0 < B) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (ha : 0 < a)
    (h0 : ∀ D x, 0 ≤ ex D x) (h1 : ∀ D x, ex D x ≤ 2 * B * s D x)
    (h2 : ∀ D x, 0 < ex D x → 0 < Δ x ∧ Δ x ≤ ex D x)
    (hnoise : ∀ δ > 0, μ {x | 0 < Δ x ∧ Δ x ≤ δ} ≤ ENNReal.ofReal ((γ * δ / B) ^ α))
    (htail : ∀ δ > 0, ∀ᵐ x ∂μ, ν {D | δ ≤ s D x} ≤
      ENNReal.ofReal (C₁ * Real.exp (-C₂ * a * δ ^ 2))) :
    ∫ D, ∫ x, ex D x ∂μ ∂ν ≤ Cst α γ C₁ C₂ * B * a ^ (-(1 + α) / 2) := by
  set u := a ^ (-(1/2:ℝ)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ha _
  set T0 := toMeasurable μ {x | 0 < Δ x ∧ Δ x ≤ 2 * B * u} with hT0def
  set T : ℕ → Set X := fun j => toMeasurable μ {x | 0 < Δ x ∧ Δ x ≤ 2 * B * (2 ^ (j + 1) * u)}
    with hTdef
  set E : ℕ → Set (ΩD × X) := fun j => {q | 2 ^ j * u ≤ s q.1 q.2} with hEdef
  have hE : ∀ j, MeasurableSet (E j) := fun j => measurableSet_le measurable_const hs
  set c0 := ENNReal.ofReal (2 * B * u) with hc0
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (2 * B * (2 ^ (j + 1) * u)) with hc
  set b : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (C₁ * Real.exp (-C₂ * a * (2 ^ j * u) ^ 2))
    with hb
  set H : ΩD × X → ℝ≥0∞ := fun q => T0.indicator (fun _ => c0) q.2 +
    ∑' j, (T j).indicator (fun _ => c j) q.2 * (E j).indicator 1 q with hH
  have hHm : Measurable H := by
    refine Measurable.add ((measurable_const.indicator (measurableSet_toMeasurable _ _)).comp
      measurable_snd) ?_
    refine Measurable.ennreal_tsum (fun j => ?_)
    exact ((measurable_const.indicator (measurableSet_toMeasurable _ _)).comp
      measurable_snd).mul (measurable_const.indicator (hE j))
  have hpt : ∀ D x, ENNReal.ofReal (ex D x) ≤ H (D, x) := by
    intro D x
    refine (decomp B u (ex D x) (s D x) (Δ x) hB hu0 (h0 D x) (h1 D x) (h2 D x)).trans ?_
    refine add_le_add ?_ (ENNReal.tsum_le_tsum (fun j => ?_))
    · split_ifs with hcnd
      · have hx : x ∈ T0 := subset_toMeasurable μ _ hcnd
        simp [Set.indicator_of_mem hx, hc0]
      · exact bot_le
    · split_ifs with hcnd
      · have hx : x ∈ T j := subset_toMeasurable μ _ hcnd.1
        have hq : (D, x) ∈ E j := hcnd.2
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hq, hc]
      · exact bot_le
  have hA : ∫⁻ D, ENNReal.ofReal (∫ x, ex D x ∂μ) ∂ν ≤ ∫⁻ x, ∫⁻ D, H (D, x) ∂ν ∂μ := by
    calc ∫⁻ D, ENNReal.ofReal (∫ x, ex D x ∂μ) ∂ν ≤ ∫⁻ D, ∫⁻ x, H (D, x) ∂μ ∂ν := by
          apply lintegral_mono
          intro D
          exact (ofReal_integral_le μ _ (h0 D)).trans (lintegral_mono (fun x => hpt D x))
      _ = _ := lintegral_lintegral_swap (f := fun D x => H (D, x)) hHm.aemeasurable
  have hsec : ∀ x j, MeasurableSet {D | 2 ^ j * u ≤ s D x} := fun x j =>
    measurableSet_le measurable_const (hs.comp (measurable_id.prodMk measurable_const))
  have hBC : ∀ᵐ x ∂μ, ∫⁻ D, H (D, x) ∂ν ≤
      T0.indicator (fun _ => c0) x + ∑' j, (T j).indicator (fun _ => c j * b j) x := by
    have hall : ∀ᵐ x ∂μ, ∀ j : ℕ, ν {D | 2 ^ j * u ≤ s D x} ≤ b j :=
      ae_all_iff.2 (fun j => htail _ (by positivity))
    filter_upwards [hall] with x hx
    simp only [hH]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    refine add_le_add le_rfl ?_
    have hmE : ∀ j, Measurable (fun D => (E j).indicator (1 : ΩD × X → ℝ≥0∞) (D, x)) := fun j =>
      (measurable_const.indicator (hE j)).comp (measurable_id.prodMk measurable_const)
    rw [lintegral_tsum (f := fun j D => (T j).indicator (fun _ => c j) x * (E j).indicator 1 (D, x))
      (fun j => ((hmE j).const_mul _).aemeasurable)]
    refine ENNReal.tsum_le_tsum (fun j => ?_)
    rw [lintegral_const_mul (f := fun D => (E j).indicator (1 : ΩD × X → ℝ≥0∞) (D, x)) _ (hmE j)]
    have : ∫⁻ D, (E j).indicator 1 (D, x) ∂ν = ν {D | 2 ^ j * u ≤ s D x} := by
      rw [← lintegral_indicator_one (hsec x j)]
      rfl
    rw [this]
    by_cases hxT : x ∈ T j
    · simp only [Set.indicator_of_mem hxT]
      gcongr
      exact hx j
    · simp [Set.indicator_of_notMem hxT]
  have hD : ∫⁻ x, (T0.indicator (fun _ => c0) x + ∑' j, (T j).indicator (fun _ => c j * b j) x) ∂μ
      = c0 * μ T0 + ∑' j, c j * b j * μ (T j) := by
    rw [lintegral_add_left (measurable_const.indicator (measurableSet_toMeasurable _ _)),
      lintegral_indicator_const (measurableSet_toMeasurable _ _),
      lintegral_tsum (fun j => (measurable_const.indicator
        (measurableSet_toMeasurable _ _)).aemeasurable)]
    congr 1
    congr 1
    ext j
    rw [lintegral_indicator_const (measurableSet_toMeasurable _ _)]
  have hT0 : μ T0 ≤ ENNReal.ofReal ((γ * (2 * B * u) / B) ^ α) := by
    rw [hT0def, measure_toMeasurable]; exact hnoise _ (by positivity)
  have hT : ∀ j, μ (T j) ≤ ENNReal.ofReal ((γ * (2 * B * (2 ^ (j + 1) * u)) / B) ^ α) := by
    intro j
    simp only [hTdef]
    rw [measure_toMeasurable]; exact hnoise _ (by positivity)
  have hnum := num_total B α γ C₁ C₂ a hB hα hγ hC₁ hC₂ ha
  rw [← hu] at hnum
  have htot : ∫⁻ D, ENNReal.ofReal (∫ x, ex D x ∂μ) ∂ν ≤
      ENNReal.ofReal (Cst α γ C₁ C₂ * B * a ^ (-(1 + α) / 2)) := by
    refine hA.trans ((lintegral_mono_ae hBC).trans ?_)
    rw [hD, ← hnum]
    refine add_le_add (by gcongr) (ENNReal.tsum_le_tsum (fun j => ?_))
    gcongr
    exact hT j
  have hF : ∀ D, 0 ≤ ∫ x, ex D x ∂μ := fun D => integral_nonneg (h0 D)
  have hK : 0 ≤ Cst α γ C₁ C₂ * B * a ^ (-(1 + α) / 2) := by
    have := Cst_nonneg α γ C₁ C₂ hγ hC₁.le
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hK).1 ((ofReal_integral_le ν _ hF).trans htot)

end Core

end RRAux_FCLO

open FastCLO.ETO in
theorem solution (α γ C₁ C₂ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C : ℝ, ∀ (p d : ℕ) (P : Polytope d) (I : Instance p d) (n : ℕ)
      (fhat pihat : (Fin n → FastCLO.ERM.Vec p × FastCLO.ERM.Vec d) → FastCLO.ERM.Vec p → FastCLO.ERM.Vec d) (a : ℝ),
      0 < a →
      NoiseCond P I α γ →
      (∀ D, IsPlugIn P (fhat D) (pihat D)) →
      Measurable (Function.uncurry fhat) →
      Measurable (Function.uncurry pihat) →
      (∀ δ > 0, ∀ᵐ x ∂I.μ,
        I.sample n {D | δ ≤ ‖fhat D x - I.fstar x‖} ≤
          ENNReal.ofReal (C₁ * Real.exp (-C₂ * a * δ ^ 2))) →
      regret P I n pihat ≤ C * P.B * a ^ (-(1 + α) / 2) := by
  refine ⟨RRAux_FCLO.Cst α γ C₁ C₂, ?_⟩
  intro p d P I n fhat pihat a ha hnoise hplug hfm _hpm htail
  have hfs : Measurable I.fstar :=
    (StronglyMeasurable.integral_kernel (κ := I.κ) (f := id) stronglyMeasurable_id).measurable
  haveI : IsProbabilityMeasure I.joint := by unfold Instance.joint; infer_instance
  haveI : IsProbabilityMeasure (I.sample n) := by unfold Instance.sample; infer_instance
  unfold regret
  exact RRAux_FCLO.core (I.sample n) I.μ
    (fun D x => ⟪I.fstar x, pihat D x⟫_ℝ - optVal P I x)
    (fun D x => ‖fhat D x - I.fstar x‖) (gap P I)
    ((hfm.sub (hfs.comp measurable_snd)).norm) P.B α γ C₁ C₂ a P.hB hα hγ hC₁ hC₂ ha
    (fun D x => RRAux_FCLO.ex_nonneg P I x _ ((hplug D).1 x).1)
    (fun D x => RRAux_FCLO.ex_le P I x (fhat D x) (pihat D x) ((hplug D).1 x).1 ((hplug D).2 x))
    (fun D x hpos => RRAux_FCLO.gap_le P I x _ ((hplug D).1 x) hpos)
    hnoise htail

#print axioms solution
