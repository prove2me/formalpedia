-- Prove2me | solution 1 for EthierKurtz.hille_yosida
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T06:49:47.911192+00:00
-- url     : https://prove2.me/submissions/d3fa141f-3f0e-4669-94aa-056949423af5

import Mathlib
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_IsInfinitesimalGenerator

set_option autoImplicit false
set_option linter.all false

open Filter
open scoped Topology

namespace Pd28fa1e3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section relation

variable (A : Submodule ℝ (E × E))

/-- Dissipativity of a linear relation. -/
def Diss : Prop := ∀ fg ∈ A, ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖

variable {A}

lemma diss_zero (hA : Diss A) {l : ℝ} (hl : 0 < l) {f g : E} (h : (f, g) ∈ A)
    (h0 : l • f - g = 0) : f = 0 := by
  have := hA (f, g) h l hl
  simp only [h0, norm_zero] at this
  have : ‖f‖ ≤ 0 := by nlinarith [norm_nonneg f]
  exact norm_le_zero_iff.mp this

/-- Step 1: dense range of `l - A` is full range, for closed dissipative `A`. -/
lemma range_full [CompleteSpace E] (hcl : IsClosed (A : Set (E × E))) (hA : Diss A) {l : ℝ}
    (hl : 0 < l) (hr : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖(l • fg.1 - fg.2) - h‖ < δ)
    (h : E) : ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  have hex : ∀ k : ℕ, ∃ fg ∈ A, ‖(l • fg.1 - fg.2) - h‖ < 1 / ((k : ℝ) + 1) :=
    fun k => hr h _ (by positivity)
  choose p hpA hpn using hex
  have hcau : ∀ m k : ℕ, ‖(p m).1 - (p k).1‖ ≤ l⁻¹ * (1 / ((m : ℝ) + 1) + 1 / ((k : ℝ) + 1)) := by
    intro m k
    have hd := hA (p m - p k) (A.sub_mem (hpA m) (hpA k)) l hl
    simp only [Prod.fst_sub, Prod.snd_sub] at hd
    have e : l • ((p m).1 - (p k).1) - ((p m).2 - (p k).2)
        = ((l • (p m).1 - (p m).2) - h) - ((l • (p k).1 - (p k).2) - h) := by
      rw [smul_sub]; abel
    rw [e] at hd
    have h2 := norm_sub_le ((l • (p m).1 - (p m).2) - h) ((l • (p k).1 - (p k).2) - h)
    rw [le_inv_mul_iff₀ hl]
    linarith [hpn m, hpn k]
  have hC : CauchySeq (fun k => (p k).1) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (l * ε))
    refine ⟨N, fun m hm => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hcau m N) ?_
    have hN' : (0 : ℝ) < N + 1 := by positivity
    have hm' : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hN' hm'
    have h3 : 2 / ((N : ℝ) + 1) < l * ε / 2 := by
      have : 4 / (l * ε) < N + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      rw [div_lt_iff₀ hN']
      nlinarith [mul_pos hl hε]
    calc l⁻¹ * (1 / ((m : ℝ) + 1) + 1 / ((N : ℝ) + 1)) ≤ l⁻¹ * (2 / ((N : ℝ) + 1)) := by
          gcongr
          rw [show (2:ℝ) / ((N:ℝ) + 1) = 1 / ((N:ℝ) + 1) + 1 / ((N:ℝ) + 1) by ring]
          linarith
      _ < l⁻¹ * (l * ε / 2) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hC
  have hres : Tendsto (fun k => (l • (p k).1 - (p k).2) - h) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hpn k).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun k => (p k).2) atTop (𝓝 (l • f - h)) := by
    have : Tendsto (fun k => l • (p k).1 - ((l • (p k).1 - (p k).2) - h) - h) atTop
        (𝓝 (l • f - 0 - h)) :=
      ((hf.const_smul l).sub hres).sub tendsto_const_nhds
    simp only [sub_zero] at this
    refine this.congr (fun k => ?_)
    abel
  have hmem : (f, l • f - h) ∈ A :=
    hcl.mem_of_tendsto (hf.prodMk_nhds hg) (Eventually.of_forall hpA)
  exact ⟨(f, l • f - h), hmem, by simp⟩

/-- Step 2: a dissipative relation with dense domain is single-valued. -/
lemma single_valued (hA : Diss A) (hd : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖fg.1 - h‖ < δ)
    {g : E} (h0 : ((0 : E), g) ∈ A) : g = 0 := by
  have key : ∀ fk ∈ A, ∀ ε : ℝ, 0 < ε → ‖fk.1‖ ≤ ‖fk.1 - g‖ + ε := by
    intro fk hfk ε hε
    set t := (‖fk.2‖ + 1) / ε with ht
    have htpos : 0 < t := by positivity
    have hmem : fk + t • ((0 : E), g) ∈ A := A.add_mem hfk (A.smul_mem t h0)
    have hdi := hA _ hmem t htpos
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero,
      add_zero] at hdi
    have e : t • fk.1 - (fk.2 + t • g) = t • (fk.1 - g) - fk.2 := by
      rw [smul_sub]; abel
    rw [e] at hdi
    have h2 : ‖t • (fk.1 - g) - fk.2‖ ≤ t * ‖fk.1 - g‖ + ‖fk.2‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg htpos.le]
    have h3 : ‖fk.2‖ ≤ t * ε := by
      rw [ht, div_mul_cancel₀ _ hε.ne']; linarith
    have : t * ‖fk.1‖ ≤ t * (‖fk.1 - g‖ + ε) := by nlinarith
    exact le_of_mul_le_mul_left this htpos
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨fk, hfk, hn⟩ := hd g (ε / 3) (by positivity)
  have h1 := key fk hfk (ε / 3) (by positivity)
  have h2 : ‖g‖ ≤ ‖fk.1‖ + ‖fk.1 - g‖ := by
    have := norm_sub_le fk.1 (fk.1 - g)
    simp only [sub_sub_cancel] at this
    linarith [norm_sub_rev fk.1 g]
  linarith

/-- Step 4: the resolvent as a bounded operator. -/
lemma exists_resolvent (hA : Diss A) {l : ℝ} (hl : 0 < l)
    (hs : ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h) :
    ∃ R : E →L[ℝ] E, (∀ h, (R h, l • R h - h) ∈ A) ∧ (∀ h, ‖R h‖ ≤ l⁻¹ * ‖h‖) := by
  have hex : ∀ h : E, ∃ f : E, (f, l • f - h) ∈ A := by
    intro h
    obtain ⟨fg, hfg, he⟩ := hs h
    refine ⟨fg.1, ?_⟩
    have : l • fg.1 - h = fg.2 := by rw [← he]; abel
    rw [this]; exact hfg
  choose r hr using hex
  have uniq : ∀ h : E, ∀ f : E, (f, l • f - h) ∈ A → r h = f := by
    intro h f hf
    have hm := A.sub_mem (hr h) hf
    have := diss_zero hA hl hm (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [smul_sub]; abel)
    exact sub_eq_zero.mp this
  let L : E →ₗ[ℝ] E :=
    { toFun := r
      map_add' := fun x y => by
        refine (uniq (x + y) (r x + r y) ?_).trans rfl
        have := A.add_mem (hr x) (hr y)
        convert this using 1
        simp only [Prod.mk_add_mk, smul_add]; congr 1; abel
      map_smul' := fun s x => by
        refine (uniq (s • x) (s • r x) ?_).trans rfl
        have := A.smul_mem s (hr x)
        convert this using 1
        simp only [Prod.smul_mk, smul_sub, smul_comm l s] }
  have hb : ∀ h, ‖r h‖ ≤ l⁻¹ * ‖h‖ := by
    intro h
    have := hA _ (hr h) l hl
    simp only [sub_sub_cancel] at this
    rw [le_inv_mul_iff₀ hl]; exact this
  exact ⟨L.mkContinuous l⁻¹ hb, fun h => hr h, hb⟩

/-- Step 3a: surjectivity of `l - A` propagates from `l₁` to `(0, 2 l₁)` (Neumann series). -/
lemma range_step [CompleteSpace E] (hA : Diss A) {l₁ : ℝ} (hl₁ : 0 < l₁)
    (hs₁ : ∀ h : E, ∃ fg ∈ A, l₁ • fg.1 - fg.2 = h) {l : ℝ} (hl : 0 < l) (hll : l < 2 * l₁) :
    ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  obtain ⟨R, hR, hRb⟩ := exists_resolvent hA hl₁ hs₁
  have hRn : ‖R‖ ≤ l₁⁻¹ := ContinuousLinearMap.opNorm_le_bound _ (by positivity) hRb
  set K : E →L[ℝ] E := (l₁ - l) • R with hK
  have hKn : ‖K‖ < 1 := by
    calc ‖K‖ ≤ |l₁ - l| * ‖R‖ := by rw [hK, norm_smul, Real.norm_eq_abs]
      _ ≤ |l₁ - l| * l₁⁻¹ := by gcongr
      _ < 1 := by
          rw [← div_eq_mul_inv, div_lt_one hl₁, abs_lt]
          constructor <;> linarith
  intro h
  set U := Units.oneSub K hKn
  set f : E := (↑U⁻¹ : E →L[ℝ] E) (R h) with hf
  have hU : f - K f = R h := by
    have e := congrArg (fun T : E →L[ℝ] E => T (R h)) (Units.mul_inv U)
    simp only [ContinuousLinearMap.mul_apply, Units.val_oneSub, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at e
    rw [← hf] at e
    exact e
  set h' : E := h + (l₁ - l) • f with hh'
  have hRf : R h' = f := by
    rw [hh', map_add, map_smul]
    have : K f = (l₁ - l) • R f := by rw [hK]; rfl
    rw [← this]
    rw [← hU]; abel
  refine ⟨(R h', l₁ • R h' - h'), hR h', ?_⟩
  show l • R h' - (l₁ • R h' - h') = h
  rw [hRf, hh', sub_smul]; abel

/-- Step 3b: full range for every positive `l`. -/
lemma range_all [CompleteSpace E] (hA : Diss A) {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hs₀ : ∀ h : E, ∃ fg ∈ A, l₀ • fg.1 - fg.2 = h) {l : ℝ} (hl : 0 < l) :
    ∀ h : E, ∃ fg ∈ A, l • fg.1 - fg.2 = h := by
  have hk : ∀ k : ℕ, ∀ h : E, ∃ fg ∈ A, (l₀ * (3 / 2 : ℝ) ^ k) • fg.1 - fg.2 = h := by
    intro k
    induction k with
    | zero => simpa using hs₀
    | succ k ih =>
      have hp : 0 < l₀ * (3 / 2 : ℝ) ^ k := by positivity
      refine range_step hA hp ih (by positivity) ?_
      rw [pow_succ]; nlinarith
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (l / l₀) (by norm_num : (1 : ℝ) < 3 / 2)
  have hp : 0 < l₀ * (3 / 2 : ℝ) ^ k := by positivity
  refine range_step hA hp (hk k) hl ?_
  rw [div_lt_iff₀ hl₀] at hk'
  nlinarith

/-- Step 4b: a resolvent family on all of `(0, ∞)`. -/
lemma resolvent_family [CompleteSpace E] (hA : Diss A) {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hs₀ : ∀ h : E, ∃ fg ∈ A, l₀ • fg.1 - fg.2 = h) :
    ∃ R : ℝ → E →L[ℝ] E, ∀ l : ℝ, 0 < l →
      (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖) := by
  have : ∀ l : ℝ, ∃ R : E →L[ℝ] E, 0 < l →
      (∀ h, (R h, l • R h - h) ∈ A) ∧ (∀ h, ‖R h‖ ≤ l⁻¹ * ‖h‖) := by
    intro l
    by_cases hl : 0 < l
    · obtain ⟨R, h1, h2⟩ := exists_resolvent hA hl (range_all hA hl₀ hs₀ hl)
      exact ⟨R, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose R hR using this
  exact ⟨R, hR⟩

/-- The resolvent inverts `l - A` on the relation. -/
lemma res_eq (hA : Diss A) {l : ℝ} (hl : 0 < l) {R : E →L[ℝ] E}
    (hR : ∀ h, (R h, l • R h - h) ∈ A) {f g : E} (hfg : (f, g) ∈ A) :
    R (l • f - g) = f := by
  have hm := A.sub_mem (hR (l • f - g)) hfg
  have := diss_zero hA hl hm (by simp only [Prod.fst_sub, Prod.snd_sub]; rw [smul_sub]; abel)
  exact sub_eq_zero.mp this

/-- Step 6a: `l R_l h → h` as `l → ∞`, using the dense domain. -/
lemma yosida_tendsto (hA : Diss A) (hd : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖fg.1 - h‖ < δ)
    {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    (h : E) : Tendsto (fun l : ℝ => l • R l h) atTop (𝓝 h) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨fg, hfg, hn⟩ := hd h (ε / 3) (by positivity)
  refine ⟨max 1 (3 * (‖fg.2‖ + 1) / ε), fun l hl => ?_⟩
  have hl1 : 0 < l := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hl)
  have hl2 : 3 * (‖fg.2‖ + 1) / ε ≤ l := (le_max_right _ _).trans hl
  obtain ⟨hR1, hR2⟩ := hR l hl1
  have hcon : ∀ x, ‖l • R l x‖ ≤ ‖x‖ := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg hl1.le]
    calc l * ‖R l x‖ ≤ l * (l⁻¹ * ‖x‖) := by gcongr; exact hR2 x
      _ = ‖x‖ := by field_simp
  have e1 : l • R l fg.1 - fg.1 = R l fg.2 := by
    have := res_eq hA hl1 hR1 hfg
    rw [map_sub, map_smul] at this
    calc l • R l fg.1 - fg.1 = l • R l fg.1 - (l • R l fg.1 - R l fg.2) := by rw [this]
      _ = R l fg.2 := by abel
  have e2 : ‖R l fg.2‖ < ε / 3 := by
    refine lt_of_le_of_lt (hR2 fg.2) ?_
    rw [inv_mul_lt_iff₀ hl1]
    rw [div_le_iff₀ hε] at hl2
    nlinarith
  rw [dist_eq_norm]
  have split : l • R l h - h = l • R l (h - fg.1) + (l • R l fg.1 - fg.1) + (fg.1 - h) := by
    rw [map_sub, smul_sub]; abel
  rw [split, e1]
  have h3 : ‖l • R l (h - fg.1)‖ < ε / 3 := by
    refine lt_of_le_of_lt (hcon _) ?_
    rw [norm_sub_rev]; exact hn
  calc ‖l • R l (h - fg.1) + R l fg.2 + (fg.1 - h)‖
      ≤ ‖l • R l (h - fg.1)‖ + ‖R l fg.2‖ + ‖fg.1 - h‖ := norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

end relation

section yosida

lemma norm_pow_le_clm (x : E →L[ℝ] E) (n : ℕ) : ‖x ^ n‖ ≤ ‖x‖ ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (by gcongr)

variable [CompleteSpace E]

lemma norm_exp_le (x : E →L[ℝ] E) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have h1 : NormedSpace.exp x = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • x ^ n := by
    rw [NormedSpace.exp_eq_tsum ℝ]
  have h2 : Real.exp ‖x‖ = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  rw [h1, h2]
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x)
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) ‖x‖).of_norm
  rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
  gcongr
  exact norm_pow_le_clm x n

/-- The Yosida semigroup `exp (t (l^2 R - l))`, written as `e^{-tl} exp (t l^2 R)`. -/
noncomputable def Ty (l : ℝ) (R : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  Real.exp (-(t * l)) • NormedSpace.exp ((t * l ^ 2) • R)

/-- The Yosida approximation `l^2 R - l`. -/
noncomputable def By (l : ℝ) (R : E →L[ℝ] E) : E →L[ℝ] E := (l ^ 2) • R - l • (1 : E →L[ℝ] E)

lemma Ty_zero (l : ℝ) (R : E →L[ℝ] E) : Ty l R 0 = 1 := by simp [Ty]

lemma Ty_add (l : ℝ) (R : E →L[ℝ] E) (s t : ℝ) : Ty l R (s + t) = Ty l R s * Ty l R t := by
  have hc : Commute ((s * l ^ 2) • R) ((t * l ^ 2) • R) :=
    ((Commute.refl R).smul_left _).smul_right _
  simp only [Ty]
  rw [show ((s + t) * l ^ 2) • R = (s * l ^ 2) • R + (t * l ^ 2) • R by rw [add_mul, add_smul],
    NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
      ((NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _), show -((s + t) * l) = -(s * l) + -(t * l) by ring,
    Real.exp_add, smul_mul_smul_comm]

lemma Ty_norm {l : ℝ} (hl : 0 < l) {R : E →L[ℝ] E} (hR : ‖R‖ ≤ l⁻¹) {t : ℝ} (ht : 0 ≤ t) :
    ‖Ty l R t‖ ≤ 1 := by
  simp only [Ty]
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : ‖NormedSpace.exp ((t * l ^ 2) • R)‖ ≤ Real.exp (t * l) := by
    refine (norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc t * l ^ 2 * ‖R‖ ≤ t * l ^ 2 * l⁻¹ := by gcongr
      _ = t * l := by
        rw [pow_two, ← mul_assoc, mul_assoc (t * l) l l⁻¹, mul_inv_cancel₀ hl.ne', mul_one]
  calc Real.exp (-(t * l)) * ‖NormedSpace.exp ((t * l ^ 2) • R)‖
      ≤ Real.exp (-(t * l)) * Real.exp (t * l) := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

lemma Ty_hasDerivAt (l : ℝ) (R : E →L[ℝ] E) (t : ℝ) :
    HasDerivAt (Ty l R) (Ty l R t * By l R) t := by
  have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(u * l))) (Real.exp (-(t * l)) * (-l)) t := by
    have := ((hasDerivAt_id t).mul_const l).neg.exp
    simpa using this
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u * l ^ 2) • R))
      (NormedSpace.exp ((t * l ^ 2) • R) * ((l ^ 2) • R)) t := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) ((l ^ 2) • R) t
    simpa [smul_smul] using this
  have h3 := h1.smul h2
  have e : Ty l R t * By l R = Real.exp (-(t * l)) • (NormedSpace.exp ((t * l ^ 2) • R) *
      ((l ^ 2) • R)) + (Real.exp (-(t * l)) * (-l)) • NormedSpace.exp ((t * l ^ 2) • R) := by
    simp only [Ty, By, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
    module
  rw [e]
  exact h3

lemma Ty_commute_By {l m : ℝ} {R R' : E →L[ℝ] E} (h : Commute R R') (s : ℝ) :
    Commute (Ty m R' s) (By l R) := by
  have h1 : Commute (Ty m R' s) R :=
    ((h.symm.smul_left _).exp_left).smul_left _
  exact (h1.smul_right _).sub_right ((Commute.one_right _).smul_right _)

/-- Mean value bound for an operator family with `T' = T B`. -/
lemma mvt_bound {T : ℝ → E →L[ℝ] E} {B : E →L[ℝ] E}
    (hT : ∀ s, HasDerivAt T (T s * B) s) {t : ℝ} (ht : 0 ≤ t) (f y : E) {C : ℝ}
    (hC : ∀ s ∈ Set.Ico (0 : ℝ) t, ‖T s (B f) - y‖ ≤ C) :
    ‖T t f - T 0 f - t • y‖ ≤ C * t := by
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) t, HasDerivWithinAt (fun u => T u f - u • y)
      (T s (B f) - y) (Set.Icc 0 t) s := by
    intro s _
    have h1 : HasDerivAt (fun u => T u f) (T s (B f)) s := by
      have := (hT s).clm_apply (hasDerivAt_const s f)
      simpa [ContinuousLinearMap.mul_apply] using this
    have h2 : HasDerivAt (fun u : ℝ => u • y) y s := by
      simpa using (hasDerivAt_id s).smul_const y
    exact (h1.sub h2).hasDerivWithinAt
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hC t ⟨ht, le_rfl⟩
  calc ‖T t f - T 0 f - t • y‖ = ‖(T t f - t • y) - (T 0 f - (0 : ℝ) • y)‖ := by
        rw [zero_smul, sub_zero, sub_right_comm]
    _ ≤ C * (t - 0) := this
    _ = C * t := by ring

/-- Mean value comparison of two commuting operator families. -/
lemma mvt_cauchy {T₁ T₂ : ℝ → E →L[ℝ] E} {B₁ B₂ : E →L[ℝ] E}
    (h₁ : ∀ s, HasDerivAt T₁ (T₁ s * B₁) s) (h₂ : ∀ s, HasDerivAt T₂ (T₂ s * B₂) s)
    (hc : ∀ u, Commute (T₂ u) B₁)
    (n₁ : ∀ s, 0 ≤ s → ‖T₁ s‖ ≤ 1) (n₂ : ∀ s, 0 ≤ s → ‖T₂ s‖ ≤ 1)
    (h01 : T₁ 0 = 1) (h02 : T₂ 0 = 1) {t : ℝ} (ht : 0 ≤ t) (f : E) :
    ‖T₁ t f - T₂ t f‖ ≤ ‖B₁ f - B₂ f‖ * t := by
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) t, HasDerivWithinAt (fun u => T₁ u (T₂ (t - u) f))
      (T₁ s (T₂ (t - s) (B₁ f - B₂ f))) (Set.Icc 0 t) s := by
    intro s _
    have hg : HasDerivAt (fun u => T₂ (t - u)) (-(T₂ (t - s) * B₂)) s := by
      have hh : HasDerivAt (fun u : ℝ => t - u) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub t
      have := (h₂ (t - s)).scomp s hh
      simpa [neg_one_smul, Function.comp_def] using this
    have hu : HasDerivAt (fun u => T₂ (t - u) f) (-(T₂ (t - s) (B₂ f))) s := by
      simpa [ContinuousLinearMap.mul_apply] using hg.clm_apply (hasDerivAt_const s f)
    have h3 := (h₁ s).clm_apply hu
    have e : (T₁ s * B₁) (T₂ (t - s) f) + T₁ s (-(T₂ (t - s) (B₂ f)))
        = T₁ s (T₂ (t - s) (B₁ f - B₂ f)) := by
      have hcf : B₁ (T₂ (t - s) f) = T₂ (t - s) (B₁ f) := by
        have := congrArg (fun T : E →L[ℝ] E => T f) (hc (t - s)).eq
        simpa [ContinuousLinearMap.mul_apply] using this.symm
      rw [ContinuousLinearMap.mul_apply, hcf, map_neg, map_sub, map_sub]
      exact (sub_eq_add_neg _ _).symm
    rw [← e]
    exact h3.hasDerivWithinAt
  have hb : ∀ s ∈ Set.Ico (0 : ℝ) t, ‖T₁ s (T₂ (t - s) (B₁ f - B₂ f))‖ ≤ ‖B₁ f - B₂ f‖ := by
    intro s hs
    calc ‖T₁ s (T₂ (t - s) (B₁ f - B₂ f))‖ ≤ ‖T₁ s‖ * ‖T₂ (t - s) (B₁ f - B₂ f)‖ :=
          (T₁ s).le_opNorm _
      _ ≤ 1 * (‖T₂ (t - s)‖ * ‖B₁ f - B₂ f‖) := by
          gcongr
          · exact n₁ s hs.1
          · exact (T₂ (t - s)).le_opNorm _
      _ ≤ 1 * (1 * ‖B₁ f - B₂ f‖) := by
          gcongr
          exact n₂ _ (by linarith [hs.2])
      _ = ‖B₁ f - B₂ f‖ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simp only [sub_self, h01, h02, sub_zero, ContinuousLinearMap.one_apply] at this
  exact this

end yosida

section assembly

variable [CompleteSpace E] {A : Submodule ℝ (E × E)}

lemma res_commute (hA : Diss A) {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    {l m : ℝ} (hl : 0 < l) (hm : 0 < m) : Commute (R l) (R m) := by
  have key : ∀ l m : ℝ, 0 < l → 0 < m → ∀ h, R m h - R l h = (l - m) • R l (R m h) := by
    intro l m hl hm h
    have hfm := (hR m hm).1 h
    have := res_eq hA hl (hR l hl).1 hfm
    have e : l • R m h - (m • R m h - h) = (l - m) • R m h + h := by rw [sub_smul]; abel
    rw [e, map_add, map_smul] at this
    exact (by rw [this] : R m h - R l h = ((l - m) • R l (R m h) + R l h) - R l h).trans
      (by abel)
  by_cases hlm : l = m
  · subst hlm; exact Commute.refl _
  show R l * R m = R m * R l
  ext h
  have h1 := key l m hl hm h
  have h2 := key m l hm hl h
  have hne : l - m ≠ 0 := sub_ne_zero.mpr hlm
  have : (l - m) • R l (R m h) = (l - m) • R m (R l h) := by
    rw [← h1, show (l - m) = -(m - l) by ring, neg_smul, ← h2]; abel
  simp only [ContinuousLinearMap.mul_apply]
  exact smul_right_injective E hne this

/-- The Yosida grid `l_k = k + 1`. -/
noncomputable def lam (k : ℕ) : ℝ := k + 1

lemma lam_pos (k : ℕ) : 0 < lam k := by unfold lam; positivity

noncomputable def Tk (R : ℝ → E →L[ℝ] E) (k : ℕ) (t : ℝ) : E →L[ℝ] E := Ty (lam k) (R (lam k)) t

noncomputable def Bk (R : ℝ → E →L[ℝ] E) (k : ℕ) : E →L[ℝ] E := By (lam k) (R (lam k))

lemma normR {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    {l : ℝ} (hl : 0 < l) : ‖R l‖ ≤ l⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hl.le) (hR l hl).2

lemma Tk_apply_le {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    (k : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖Tk R k t x‖ ≤ ‖x‖ :=
  ((Tk R k t).le_opNorm x).trans
    (mul_le_of_le_one_left (norm_nonneg x) (Ty_norm (lam_pos k) (normR hR (lam_pos k)) ht))

lemma Bk_A (hA : Diss A) {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    (k : ℕ) {f g : E} (hfg : (f, g) ∈ A) : Bk R k f = lam k • R (lam k) g := by
  have hl := lam_pos k
  have := res_eq hA hl (hR (lam k) hl).1 hfg
  rw [map_sub, map_smul] at this
  have e1 : lam k • R (lam k) f - f = R (lam k) g := by
    calc lam k • R (lam k) f - f = lam k • R (lam k) f - (lam k • R (lam k) f - R (lam k) g) := by
          rw [this]
      _ = R (lam k) g := by abel
  simp only [Bk, By, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  rw [← e1, smul_sub, smul_smul, pow_two]

lemma Bk_le (hA : Diss A) {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    (k : ℕ) {f g : E} (hfg : (f, g) ∈ A) : ‖Bk R k f‖ ≤ ‖g‖ := by
  have hl := lam_pos k
  rw [Bk_A hA hR k hfg, norm_smul, Real.norm_of_nonneg hl.le]
  calc lam k * ‖R (lam k) g‖ ≤ lam k * ((lam k)⁻¹ * ‖g‖) := by gcongr; exact (hR _ hl).2 g
    _ = ‖g‖ := by field_simp

lemma Bk_tendsto (hA : Diss A) (hd : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖fg.1 - h‖ < δ)
    {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    {f g : E} (hfg : (f, g) ∈ A) : Tendsto (fun k => Bk R k f) atTop (𝓝 g) := by
  have hlam : Tendsto lam atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have := (yosida_tendsto hA hd hR g).comp hlam
  refine this.congr (fun k => ?_)
  simp only [Function.comp_apply]
  rw [Bk_A hA hR k hfg]

lemma Tk_deriv (R : ℝ → E →L[ℝ] E) (k : ℕ) (s : ℝ) :
    HasDerivAt (Tk R k) (Tk R k s * Bk R k) s := Ty_hasDerivAt _ _ s

lemma Tk_D (hA : Diss A) {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    (k : ℕ) {t : ℝ} (ht : 0 ≤ t) {f g : E} (hfg : (f, g) ∈ A) :
    ‖Tk R k t f - f‖ ≤ ‖g‖ * t := by
  have := mvt_bound (Tk_deriv R k) ht f 0 (C := ‖g‖) (fun s hs => by
    rw [sub_zero]; exact (Tk_apply_le hR k hs.1 _).trans (Bk_le hA hR k hfg))
  simpa [Tk, Ty_zero] using this

lemma Tk_cauchy (hA : Diss A) (hd : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖fg.1 - h‖ < δ)
    {R : ℝ → E →L[ℝ] E}
    (hR : ∀ l : ℝ, 0 < l → (∀ h, (R l h, l • R l h - h) ∈ A) ∧ (∀ h, ‖R l h‖ ≤ l⁻¹ * ‖h‖))
    {t : ℝ} (ht : 0 ≤ t) (x : E) : CauchySeq (fun k => Tk R k t x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨fg, hfg, hn⟩ := hd x (ε / 4) (by positivity)
  have hc : CauchySeq (fun k => Bk R k fg.1) := (Bk_tendsto hA hd hR hfg).cauchySeq
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨N, hN⟩ := hc (ε / (2 * (t + 1))) (by positivity)
  refine ⟨N, fun j hj k hk => ?_⟩
  rw [dist_eq_norm]
  have e : Tk R j t x - Tk R k t x = Tk R j t (x - fg.1) - Tk R k t (x - fg.1)
      + (Tk R j t fg.1 - Tk R k t fg.1) := by
    simp only [map_sub]; abel
  have hx : ‖x - fg.1‖ < ε / 4 := by rw [norm_sub_rev]; exact hn
  have h1 := Tk_apply_le hR j ht (x - fg.1)
  have h2 := Tk_apply_le hR k ht (x - fg.1)
  have h3 : ‖Tk R j t fg.1 - Tk R k t fg.1‖ ≤ ‖Bk R j fg.1 - Bk R k fg.1‖ * t :=
    mvt_cauchy (Tk_deriv R j) (Tk_deriv R k)
      (fun u => Ty_commute_By (res_commute hA hR (lam_pos j) (lam_pos k)) u)
      (fun s hs => Ty_norm (lam_pos j) (normR hR (lam_pos j)) hs)
      (fun s hs => Ty_norm (lam_pos k) (normR hR (lam_pos k)) hs)
      (Ty_zero _ _) (Ty_zero _ _) ht fg.1
  have h4 : ‖Bk R j fg.1 - Bk R k fg.1‖ * t ≤ ε / (2 * (t + 1)) * t := by
    have := hN j hj k hk
    rw [dist_eq_norm] at this
    gcongr
  have ht1 : t + 1 ≠ 0 := by linarith
  have h5 : ε / (2 * (t + 1)) * t ≤ ε / 2 := by
    calc ε / (2 * (t + 1)) * t ≤ ε / (2 * (t + 1)) * (t + 1) := by gcongr; linarith
      _ = ε / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ ht1]
  rw [e]
  calc ‖Tk R j t (x - fg.1) - Tk R k t (x - fg.1) + (Tk R j t fg.1 - Tk R k t fg.1)‖
      ≤ ‖Tk R j t (x - fg.1)‖ + ‖Tk R k t (x - fg.1)‖ + ‖Tk R j t fg.1 - Tk R k t fg.1‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ < ε / 4 + ε / 4 + ε / 2 := by linarith
    _ = ε := by ring

/-- Uniform small-time continuity for a family of contractions controlled on the domain. -/
lemma unif_of (hd : ∀ h : E, ∀ δ : ℝ, 0 < δ → ∃ fg ∈ A, ‖fg.1 - h‖ < δ)
    {ι : Type*} (S : ι → ℝ → E →L[ℝ] E)
    (hS1 : ∀ i s, 0 ≤ s → ∀ y, ‖S i s y‖ ≤ ‖y‖)
    (hS2 : ∀ i s, 0 ≤ s → ∀ f g, (f, g) ∈ A → ‖S i s f - f‖ ≤ ‖g‖ * s) (x : E) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ i s, 0 ≤ s → s ≤ δ → ‖S i s x - x‖ ≤ ε := by
  obtain ⟨fg, hfg, hn⟩ := hd x (ε / 3) (by positivity)
  refine ⟨ε / 3 / (‖fg.2‖ + 1), by positivity, fun i s hs hsδ => ?_⟩
  have e : S i s x - x = S i s (x - fg.1) + (S i s fg.1 - fg.1) + (fg.1 - x) := by
    rw [map_sub]; abel
  have h1 : ‖S i s (x - fg.1)‖ ≤ ε / 3 :=
    (hS1 i s hs _).trans (by rw [norm_sub_rev]; exact hn.le)
  have h2 : ‖S i s fg.1 - fg.1‖ ≤ ε / 3 := by
    refine (hS2 i s hs _ _ hfg).trans ?_
    have hq : (‖fg.2‖ + 1) * (ε / 3 / (‖fg.2‖ + 1)) = ε / 3 := by field_simp
    calc ‖fg.2‖ * s ≤ (‖fg.2‖ + 1) * (ε / 3 / (‖fg.2‖ + 1)) := by gcongr <;> linarith
      _ = ε / 3 := hq
  rw [e]
  calc ‖S i s (x - fg.1) + (S i s fg.1 - fg.1) + (fg.1 - x)‖
      ≤ ‖S i s (x - fg.1)‖ + ‖S i s fg.1 - fg.1‖ + ‖fg.1 - x‖ := norm_add₃_le
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-- A contraction semigroup's generator is dissipative: `(u, u)` in it forces `u = 0`. -/
lemma gen_diss {T : ℝ → E →L[ℝ] E} (hTn : ∀ t : ℝ, 0 ≤ t → ∀ x, ‖T t x‖ ≤ ‖x‖) {u : E}
    (hu : Tendsto (fun t : ℝ => t⁻¹ • (T t u - u)) (𝓝[>] (0 : ℝ)) (𝓝 u)) : u = 0 := by
  have key : ∀ t : ℝ, 0 < t → ‖u‖ ≤ ‖u - (1 / 2 : ℝ) • (t⁻¹ • (T t u - u))‖ := by
    intro t ht
    have hc0 : 0 ≤ 1 / 2 * t⁻¹ := by positivity
    have e : u - (1 / 2 : ℝ) • (t⁻¹ • (T t u - u))
        = (1 + 1 / 2 * t⁻¹) • u - (1 / 2 * t⁻¹) • T t u := by module
    rw [e]
    have h1 := norm_sub_norm_le ((1 + 1 / 2 * t⁻¹) • u) ((1 / 2 * t⁻¹) • T t u)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg hc0] at h1
    have h2 := hTn t ht.le u
    nlinarith
  have hlim : Tendsto (fun t : ℝ => ‖u - (1 / 2 : ℝ) • (t⁻¹ • (T t u - u))‖) (𝓝[>] (0 : ℝ))
      (𝓝 ‖u - (1 / 2 : ℝ) • u‖) :=
    (tendsto_const_nhds.sub (hu.const_smul (1 / 2 : ℝ))).norm
  have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => key t ht)
  have e2 : u - (1 / 2 : ℝ) • u = (1 / 2 : ℝ) • u := by module
  rw [e2, norm_smul, Real.norm_of_nonneg (by norm_num)] at this
  exact norm_le_zero_iff.mp (by linarith [norm_nonneg u])

theorem hy_main (hcl : IsClosed (A : Set (E × E))) (hA : Diss A)
    (hrange : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : E, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ A, ‖(lam₀ • fg.1 - fg.2) - h‖ < delta)
    (hd : ∀ h : E, ∀ delta : ℝ, 0 < delta → ∃ fg ∈ A, ‖fg.1 - h‖ < delta) :
    ∃ T : ℝ → E →L[ℝ] E,
      EthierKurtz.IsStronglyContinuousContractionSemigroup T ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by
  obtain ⟨l₀, hl₀, hr₀⟩ := hrange
  obtain ⟨R, hR⟩ := resolvent_family hA hl₀ (range_full hcl hA hl₀ hr₀)
  have hlim : ∀ t : ℝ, ∃ T : E →L[ℝ] E, 0 ≤ t →
      ∀ x, Tendsto (fun k => Tk R k t x) atTop (𝓝 (T x)) := by
    intro t
    by_cases ht : 0 ≤ t
    · have hc : ∀ x, ∃ y, Tendsto (fun k => Tk R k t x) atTop (𝓝 y) :=
        fun x => cauchySeq_tendsto_of_complete (Tk_cauchy hA hd hR ht x)
      choose L hL using hc
      exact ⟨continuousLinearMapOfTendsto (fun k => Tk R k t) (tendsto_pi_nhds.mpr hL),
        fun _ x => hL x⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose T hT using hlim
  have hTn : ∀ t : ℝ, 0 ≤ t → ∀ x, ‖T t x‖ ≤ ‖x‖ := fun t ht x =>
    le_of_tendsto (hT t ht x).norm (Eventually.of_forall fun k => Tk_apply_le hR k ht x)
  have hTD : ∀ t : ℝ, 0 ≤ t → ∀ f g, (f, g) ∈ A → ‖T t f - f‖ ≤ ‖g‖ * t := fun t ht f g hfg =>
    le_of_tendsto ((hT t ht f).sub_const f).norm
      (Eventually.of_forall fun k => Tk_D hA hR k ht hfg)
  -- generator contains A
  have hgen : ∀ f g, (f, g) ∈ A →
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[>] (0 : ℝ)) (𝓝 g) := by
    intro f g hfg
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδb⟩ := unif_of hd (Tk R) (fun i s hs y => Tk_apply_le hR i hs y)
      (fun i s hs f g hfg => Tk_D hA hR i hs hfg) g (ε := ε / 2) (by positivity)
    refine ⟨δ, hδ, fun {t} ht hdt => ?_⟩
    have ht0 : 0 < t := ht
    have htδ : t ≤ δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at hdt; exact hdt.le
    have hk : ∀ k, ‖Tk R k t f - f - t • Bk R k f‖ ≤ (2 * ‖Bk R k f - g‖ + ε / 2) * t := by
      intro k
      have := mvt_bound (Tk_deriv R k) ht0.le f (Bk R k f)
        (C := 2 * ‖Bk R k f - g‖ + ε / 2) (fun s hs => by
          have e : Tk R k s (Bk R k f) - Bk R k f
              = Tk R k s (Bk R k f - g) + (Tk R k s g - g) + (g - Bk R k f) := by
            rw [map_sub]; abel
          rw [e]
          have h1 := Tk_apply_le hR k hs.1 (Bk R k f - g)
          have h2 := hδb k s hs.1 (hs.2.le.trans htδ)
          have h3 : ‖g - Bk R k f‖ = ‖Bk R k f - g‖ := norm_sub_rev _ _
          calc ‖Tk R k s (Bk R k f - g) + (Tk R k s g - g) + (g - Bk R k f)‖
              ≤ ‖Tk R k s (Bk R k f - g)‖ + ‖Tk R k s g - g‖ + ‖g - Bk R k f‖ := norm_add₃_le
            _ ≤ 2 * ‖Bk R k f - g‖ + ε / 2 := by linarith)
      simpa [Tk, Ty_zero] using this
    have hBt := Bk_tendsto hA hd hR hfg
    have hL : Tendsto (fun k => ‖Tk R k t f - f - t • Bk R k f‖) atTop
        (𝓝 ‖T t f - f - t • g‖) :=
      (((hT t ht0.le f).sub_const f).sub (hBt.const_smul t)).norm
    have hRt : Tendsto (fun k => (2 * ‖Bk R k f - g‖ + ε / 2) * t) atTop
        (𝓝 ((2 * ‖g - g‖ + ε / 2) * t)) :=
      ((((hBt.sub_const g).norm).const_mul 2).add_const (ε / 2)).mul_const t
    have hle := le_of_tendsto_of_tendsto' hL hRt hk
    rw [sub_self, norm_zero, mul_zero, zero_add] at hle
    rw [dist_eq_norm]
    have e : t⁻¹ • (T t f - f) - g = t⁻¹ • (T t f - f - t • g) := by
      rw [smul_sub (t⁻¹) _ (t • g), smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
    calc t⁻¹ * ‖T t f - f - t • g‖ ≤ t⁻¹ * (ε / 2 * t) := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  refine ⟨T, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · ext x
    have h0 : Tendsto (fun k => Tk R k 0 x) atTop (𝓝 x) := by
      simp only [Tk, Ty_zero, ContinuousLinearMap.one_apply]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (hT 0 le_rfl x) h0
  · intro s t hs ht
    ext x
    show T (s + t) x = T s (T t x)
    have h2 : Tendsto (fun k => Tk R k (s + t) x) atTop (𝓝 (T s (T t x))) := by
      have h3 : Tendsto (fun k => Tk R k s (Tk R k t x - T t x)) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun k => Tk_apply_le hR k hs _) ?_
        exact (tendsto_iff_norm_sub_tendsto_zero.mp (hT t ht x))
      have h4 := h3.add (hT s hs (T t x))
      rw [zero_add] at h4
      refine h4.congr (fun k => ?_)
      rw [← map_add, sub_add_cancel]
      show Tk R k s (Tk R k t x) = Ty (lam k) (R (lam k)) (s + t) x
      rw [Ty_add, ContinuousLinearMap.mul_apply]
      rfl
    exact tendsto_nhds_unique (hT (s + t) (add_nonneg hs ht) x) h2
  · intro t ht
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      rw [one_mul]; exact hTn t ht x)
  · intro x
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδb⟩ := unif_of hd (fun _ : Unit => T) (fun _ s hs y => hTn s hs y)
      (fun _ s hs f g hfg => hTD s hs f g hfg) x (ε := ε / 2) (by positivity)
    refine ⟨δ, hδ, fun {t} ht hdt => ?_⟩
    have ht0 : 0 < t := ht
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at hdt
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hδb () t ht0.le hdt.le) (by linarith)
  · intro f g
    refine ⟨fun hfg => ?_, fun hfg => hgen f g hfg⟩
    have hf' := (hR 1 one_pos).1 (f - g)
    have hg' := hgen _ _ hf'
    have hu : Tendsto (fun t : ℝ => t⁻¹ • (T t (f - R 1 (f - g)) - (f - R 1 (f - g))))
        (𝓝[>] (0 : ℝ)) (𝓝 (f - R 1 (f - g))) := by
      have := hfg.sub hg'
      have e : g - ((1 : ℝ) • R 1 (f - g) - (f - g)) = f - R 1 (f - g) := by
        rw [one_smul]; abel
      rw [e] at this
      refine this.congr (fun t => ?_)
      rw [← smul_sub, map_sub (T t) f (R 1 (f - g))]; congr 1; abel
    have h0 := gen_diss hTn hu
    have hf : f = R 1 (f - g) := sub_eq_zero.mp h0
    have : (f, g) = (R 1 (f - g), (1 : ℝ) • R 1 (f - g) - (f - g)) := by
      refine Prod.ext hf ?_
      show g = (1 : ℝ) • R 1 (f - g) - (f - g)
      rw [one_smul, ← hf]; abel
    rw [this]; exact hf'

end assembly

end Pd28fa1e3

namespace Pd28fa1e3B

open Pd28fa1e3

section semigroup
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

structure SG (T : ℝ → V →L[ℝ] V) : Prop where
  zero : T 0 = ContinuousLinearMap.id ℝ V
  add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  contr : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1
  cont : ∀ f : V, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f)

def IsGen (T : ℝ → V →L[ℝ] V) (h g : V) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (T t h - h)) (𝓝[>] (0 : ℝ)) (𝓝 g)

variable {T : ℝ → V →L[ℝ] V}

lemma SG.apply_le (hT : SG T) {t : ℝ} (ht : 0 ≤ t) (x : V) : ‖T t x‖ ≤ ‖x‖ := by
  calc ‖T t x‖ ≤ ‖T t‖ * ‖x‖ := (T t).le_opNorm x
    _ ≤ 1 * ‖x‖ := by gcongr; exact hT.contr t ht
    _ = ‖x‖ := one_mul _

lemma SG.add_apply (hT : SG T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : V) :
    T (s + t) x = T s (T t x) := by
  rw [hT.add s t hs ht]; rfl

lemma SG.comm (hT : SG T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : V) :
    T s (T t x) = T t (T s x) := by
  rw [← hT.add_apply hs ht, ← hT.add_apply ht hs, add_comm]

lemma SG.dist_le (hT : SG T) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (x : V) :
    ‖T w x - T v x‖ ≤ ‖T (w - v) x - x‖ := by
  have : T w x = T v (T (w - v) x) := by
    rw [← hT.add_apply hv (by linarith), show v + (w - v) = w by ring]
  rw [this, ← map_sub]
  exact hT.apply_le hv _

lemma SG.tendsto_zero (hT : SG T) (x : V) :
    Tendsto (fun δ : ℝ => ‖T δ x - x‖) (𝓝[>] 0) (𝓝 0) := by
  have := (hT.cont x).sub_const x
  simp only [sub_self] at this
  exact tendsto_norm_zero.comp this

lemma SG.continuousOn (hT : SG T) (x : V) : ContinuousOn (fun v => T v x) (Set.Ici 0) := by
  intro v0 hv0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hT.tendsto_zero x) ε hε
  refine ⟨δ, hδ, fun {v} hv hd => ?_⟩
  simp only [Set.mem_Ici] at hv hv0
  have key : ∀ a b : ℝ, 0 ≤ a → a < b → b - a < δ → dist (T b x) (T a x) < ε := by
    intro a b ha hab hba
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hT.dist_le ha hab.le x) ?_
    have h1 := hδ' (x := b - a) (Set.mem_Ioi.2 (by linarith))
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    simpa [Real.dist_eq] using h1
  rw [Real.dist_eq, abs_lt] at hd
  rcases lt_trichotomy v v0 with h | h | h
  · rw [dist_comm]; exact key v v0 hv h (by linarith)
  · subst h; simpa using hε
  · exact key v0 v hv0 h (by linarith)

lemma SG.isGen_apply (hT : SG T) {v : ℝ} (hv : 0 ≤ v) {h g : V} (hg : IsGen T h g) :
    IsGen T (T v h) (T v g) := by
  have := ((T v).continuous.tendsto g).comp hg
  refine this.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  simp only [Function.comp_apply, map_smul, map_sub]
  rw [hT.comm hv (le_of_lt ht)]

lemma fwd_diss (hT : SG T) {x y : V} (hg : IsGen T x y) {r : ℝ} (hr : 0 < r) :
    r * ‖x‖ ≤ ‖r • x - y‖ := by
  have hlim : Tendsto (fun t : ℝ => ‖r • x - t⁻¹ • (T t x - x)‖) (𝓝[>] 0) (𝓝 ‖r • x - y‖) :=
    (tendsto_const_nhds.sub hg).norm
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
  have h1 : ‖T t x‖ ≤ ‖x‖ := hT.apply_le ht.le x
  have e : r • x - t⁻¹ • (T t x - x) = t⁻¹ • ((1 + r * t) • x - T t x) := by
    rw [add_smul, one_smul, smul_sub, smul_sub, smul_add, smul_smul t⁻¹ (r * t),
      show t⁻¹ * (r * t) = r by field_simp]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
  have h2 := norm_sub_norm_le ((1 + r * t) • x) (T t x)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h2
  nlinarith [norm_nonneg x]

lemma gcont (hT : SG T) (y : V) : Continuous (fun s : ℝ => T (max s 0) y) :=
  (hT.continuousOn y).comp_continuous (continuous_id.max continuous_const)
    (fun s => le_max_right s 0)

variable [CompleteSpace V]

noncomputable def Gi (T : ℝ → V →L[ℝ] V) (y : V) (u : ℝ) : V := ∫ s in (0:ℝ)..u, T (max s 0) y

lemma Gi_zero (y : V) : Gi T y 0 = 0 := by simp [Gi]

lemma Gi_deriv (hT : SG T) (y : V) (u : ℝ) : HasDerivAt (Gi T y) (T (max u 0) y) u :=
  ((gcont hT y).integral_hasStrictDerivAt 0 u).hasDerivAt

lemma Gi_shift (hT : SG T) (y : V) {t : ℝ} (ht : 0 ≤ t) {h : ℝ} (hh : 0 ≤ h) :
    T t (Gi T y h) = Gi T y (h + t) - Gi T y t := by
  unfold Gi
  rw [← (T t).intervalIntegral_comp_comm ((gcont hT y).intervalIntegrable 0 h)]
  have e : ∫ s in (0:ℝ)..h, T t (T (max s 0) y) = ∫ s in (0:ℝ)..h, T (max (s + t) 0) y := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le hh] at hs
    rw [max_eq_left hs.1, max_eq_left (by linarith [hs.1]), ← hT.add_apply ht hs.1, add_comm]
  have e2 := intervalIntegral.integral_comp_add_right (fun s => T (max s 0) y) t (a := 0) (b := h)
  rw [e, e2, zero_add]
  exact (intervalIntegral.integral_interval_sub_left ((gcont hT y).intervalIntegrable _ _)
    ((gcont hT y).intervalIntegrable _ _)).symm

lemma avg_gen (hT : SG T) (y : V) {h : ℝ} (hh : 0 < h) :
    IsGen T (h⁻¹ • Gi T y h) (h⁻¹ • (T h y - y)) := by
  have d1 := (Gi_deriv hT y h).tendsto_slope_zero_right
  have d0 := (Gi_deriv hT y 0).tendsto_slope_zero_right
  have hlim := (d1.sub d0).const_smul h⁻¹
  rw [max_eq_left hh.le, max_self, hT.zero, ContinuousLinearMap.id_apply] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
  beta_reduce
  rw [map_smul, Gi_shift hT y ht.le hh.le, Gi_zero, zero_add, sub_zero]
  module

lemma avg_dense (hT : SG T) (y : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ v w : V, IsGen T v w ∧ ‖v - y‖ < ε := by
  have d0 := (Gi_deriv hT y 0).tendsto_slope_zero_right
  rw [max_self, hT.zero, ContinuousLinearMap.id_apply] at d0
  obtain ⟨h, hlt, hh⟩ :=
    ((d0.eventually (Metric.ball_mem_nhds y hε)).and self_mem_nhdsWithin).exists
  refine ⟨h⁻¹ • Gi T y h, _, avg_gen hT y hh, ?_⟩
  simp only [zero_add, Gi_zero, sub_zero] at hlt
  rwa [dist_eq_norm] at hlt

noncomputable def fe (T : ℝ → V →L[ℝ] V) (y : V) (s : ℝ) : V := Real.exp (-s) • T (max s 0) y

lemma fe_cont (hT : SG T) (y : V) : Continuous (fe T y) :=
  (Real.continuous_exp.comp continuous_neg).smul (gcont hT y)

lemma fe_int (hT : SG T) (y : V) : MeasureTheory.IntegrableOn (fe T y) (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono' ((integrableOn_exp_neg_Ioi 0).mul_const ‖y‖)
    (fe_cont hT y).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  simp only [fe, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (hT.apply_le (le_max_right s 0) y) (Real.exp_pos _).le

noncomputable def Fe (T : ℝ → V →L[ℝ] V) (y : V) (u : ℝ) : V := ∫ s in (0:ℝ)..u, fe T y s

noncomputable def Re (T : ℝ → V →L[ℝ] V) (y : V) : V := ∫ s in Set.Ioi (0:ℝ), fe T y s

lemma Fe_shift (hT : SG T) (y : V) {t : ℝ} (ht : 0 ≤ t) {b : ℝ} (hb : 0 ≤ b) :
    T t (Fe T y b) = Real.exp t • (Fe T y (b + t) - Fe T y t) := by
  unfold Fe
  rw [← (T t).intervalIntegral_comp_comm ((fe_cont hT y).intervalIntegrable 0 b)]
  have e : ∫ s in (0:ℝ)..b, T t (fe T y s) = ∫ s in (0:ℝ)..b, Real.exp t • fe T y (s + t) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le hb] at hs
    simp only [fe, map_smul]
    rw [max_eq_left hs.1, max_eq_left (by linarith [hs.1]), smul_smul, ← Real.exp_add,
      show t + -(s + t) = -s by ring, ← hT.add_apply ht hs.1, add_comm t s]
  have e2 := intervalIntegral.integral_comp_add_right (fe T y) t (a := 0) (b := b)
  rw [e, intervalIntegral.integral_smul, e2, zero_add,
    intervalIntegral.integral_interval_sub_left ((fe_cont hT y).intervalIntegrable _ _)
      ((fe_cont hT y).intervalIntegrable _ _)]

lemma Re_shift (hT : SG T) (y : V) {t : ℝ} (ht : 0 ≤ t) :
    T t (Re T y) = Real.exp t • (Re T y - Fe T y t) := by
  have hR : Tendsto (Fe T y) atTop (𝓝 (Re T y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 (fe_int hT y) tendsto_id
  have h1 : Tendsto (fun b => T t (Fe T y b)) atTop (𝓝 (T t (Re T y))) :=
    ((T t).continuous.tendsto _).comp hR
  have h2 : Tendsto (fun b => Real.exp t • (Fe T y (b + t) - Fe T y t)) atTop
      (𝓝 (Real.exp t • (Re T y - Fe T y t))) :=
    ((hR.comp (tendsto_atTop_add_const_right _ t tendsto_id)).sub_const _).const_smul _
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [eventually_ge_atTop 0] with b hb
  exact (Fe_shift hT y ht hb).symm

lemma res_gen (hT : SG T) (y : V) : IsGen T (Re T y) (Re T y - y) := by
  have dF : Tendsto (fun t : ℝ => t⁻¹ • (Fe T y (0 + t) - Fe T y 0)) (𝓝[>] 0) (𝓝 (fe T y 0)) :=
    ((fe_cont hT y).integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  have dE := (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  have hc : Tendsto (fun t : ℝ => Real.exp t) (𝓝[>] 0) (𝓝 (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := (dE.smul_const (Re T y)).sub (hc.smul dF)
  have hv : Real.exp 0 • Re T y - Real.exp 0 • fe T y 0 = Re T y - y := by
    simp [fe, hT.zero]
  rw [hv] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
  have hF0 : Fe T y 0 = 0 := by simp [Fe]
  beta_reduce
  simp only [zero_add, hF0, sub_zero, Real.exp_zero, smul_eq_mul]
  rw [Re_shift hT y ht.le]
  module

end semigroup

section glue
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def graphSub (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) : Submodule ℝ (E × E) :=
  LinearMap.range (D.subtype.prod A)

lemma mem_graphSub {D : Submodule ℝ E} {A : D →ₗ[ℝ] E} {x y : E} :
    (x, y) ∈ graphSub D A ↔ ∃ hx : x ∈ D, A ⟨x, hx⟩ = y := by
  constructor
  · rintro ⟨⟨z, hz⟩, hzz⟩
    have h1 : z = x := congrArg Prod.fst hzz
    have h2 : A ⟨z, hz⟩ = y := congrArg Prod.snd hzz
    subst h1
    exact ⟨hz, h2⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

lemma graph_closed {D : Submodule ℝ E} {A : D →ₗ[ℝ] E}
    (hdiss : ∀ r : ℝ, 0 < r → ∀ x : D, r * ‖(x : E)‖ ≤ ‖r • (x : E) - A x‖)
    {r : ℝ} (hr : 0 < r) (hs : Function.Surjective (fun x : D => r • (x : E) - A x)) :
    IsClosed ((graphSub D A : Submodule ℝ (E × E)) : Set (E × E)) := by
  rw [← isSeqClosed_iff_isClosed]
  rintro u ⟨p1, p2⟩ hu hlim
  obtain ⟨⟨z0, hz0⟩, hz⟩ := hs (r • p1 - p2)
  simp only at hz
  have key : ∀ x : D, ‖(x : E)‖ ≤ r⁻¹ * ‖r • (x : E) - A x‖ := by
    intro x; rw [le_inv_mul_iff₀ hr]; exact hdiss r hr x
  have hu' : ∀ n, ((u n).1, (u n).2) ∈ graphSub D A := fun n => hu n
  choose hx hxA using fun n => mem_graphSub.1 (hu' n)
  have hconv : Tendsto (fun n => r • (u n).1 - (u n).2) atTop (𝓝 (r • p1 - p2)) :=
    ((hlim.fst_nhds).const_smul r).sub hlim.snd_nhds
  have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 z0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ n, ‖(u n).1 - z0‖ ≤ r⁻¹ * ‖(r • (u n).1 - (u n).2) - (r • p1 - p2)‖ := by
      intro n
      have := key (⟨(u n).1, hx n⟩ - ⟨z0, hz0⟩)
      have e : r • ((⟨(u n).1, hx n⟩ - ⟨z0, hz0⟩ : D) : E) - A (⟨(u n).1, hx n⟩ - ⟨z0, hz0⟩)
          = (r • (u n).1 - (u n).2) - (r • p1 - p2) := by
        rw [map_sub, hxA n, ← hz, Submodule.coe_sub]
        simp only [Submodule.coe_mk]
        module
      rw [e] at this
      simpa using this
    have h0 : Tendsto (fun n => r⁻¹ * ‖(r • (u n).1 - (u n).2) - (r • p1 - p2)‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hconv).const_mul r⁻¹
      simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) hb h0
  have hp1 : p1 = z0 := tendsto_nhds_unique hlim.fst_nhds h1
  subst hp1
  exact mem_graphSub.2 ⟨hz0, by simpa using hz⟩

theorem backward [CompleteSpace E] (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (hdense : Dense (D : Set E))
    (hdiss : ∀ r : ℝ, 0 < r → ∀ x : D, r * ‖(x : E)‖ ≤ ‖r • (x : E) - A x‖)
    (hsurj : ∃ r : ℝ, 0 < r ∧ Function.Surjective (fun x : D => r • (x : E) - A x)) :
    ∃ T : ℝ → E →L[ℝ] E, EthierKurtz.IsStronglyContinuousContractionSemigroup T ∧
      EthierKurtz.IsInfinitesimalGenerator D A T := by
  obtain ⟨r, hr, hs⟩ := hsurj
  have hG : Diss (graphSub D A) := by
    rintro ⟨x, y⟩ hxy lam hl
    obtain ⟨hx, rfl⟩ := mem_graphSub.1 hxy
    exact hdiss lam hl ⟨x, hx⟩
  obtain ⟨T, hT, hgen⟩ := hy_main (graph_closed hdiss hr hs) hG
    ⟨r, hr, fun h δ hδ => by
      obtain ⟨z, hz⟩ := hs h
      simp only at hz
      exact ⟨((z : E), A z), mem_graphSub.2 ⟨z.2, rfl⟩, by simpa [hz] using hδ⟩⟩
    (fun h δ hδ => by
      obtain ⟨z, hzb, hzD⟩ := Metric.dense_iff.1 hdense h δ hδ
      refine ⟨(z, A ⟨z, hzD⟩), mem_graphSub.2 ⟨hzD, rfl⟩, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm] at hzb
      exact hzb)
  exact ⟨T, hT, fun x y => (hgen x y).trans mem_graphSub⟩

theorem forward_of [CompleteSpace E] (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) (T : ℝ → E →L[ℝ] E)
    (hT : EthierKurtz.IsStronglyContinuousContractionSemigroup T)
    (hgen : EthierKurtz.IsInfinitesimalGenerator D A T)
    (hres : SG T → ∀ y : E, ∃ v : E, IsGen T v (v - y)) :
    Dense (D : Set E) ∧
      (∀ r : ℝ, 0 < r → ∀ x : D, r * ‖(x : E)‖ ≤ ‖r • (x : E) - A x‖) ∧
      (∃ r : ℝ, 0 < r ∧ Function.Surjective (fun x : D => r • (x : E) - A x)) := by
  have hS : SG T := ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2⟩
  refine ⟨Metric.dense_iff.2 fun y ε hε => ?_, fun r hr x => ?_, ⟨1, one_pos, fun y => ?_⟩⟩
  · obtain ⟨v, w, hg, hv⟩ := avg_dense hS y hε
    obtain ⟨hx, -⟩ := (hgen v w).1 hg
    exact ⟨v, by rw [Metric.mem_ball, dist_eq_norm]; exact hv, hx⟩
  · exact fwd_diss hS ((hgen x (A x)).2 ⟨x.2, rfl⟩) hr
  · obtain ⟨v, hv⟩ := hres hS y
    obtain ⟨hx, hA⟩ := (hgen v (v - y)).1 hv
    refine ⟨⟨v, hx⟩, ?_⟩
    show (1 : ℝ) • v - A ⟨v, hx⟩ = y
    rw [hA, one_smul]; abel

end glue

end Pd28fa1e3B

open EthierKurtz Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) :
    (∃ T : ℝ → E →L[ℝ] E,
      IsStronglyContinuousContractionSemigroup T ∧ IsInfinitesimalGenerator D A T) ↔
    Dense (D : Set E) ∧
      (∀ r : ℝ, 0 < r → ∀ x : D, r * ‖(x : E)‖ ≤ ‖r • (x : E) - A x‖) ∧
      (∃ r : ℝ, 0 < r ∧ Function.Surjective (fun x : D => r • (x : E) - A x)) := by
  constructor
  · rintro ⟨T, hT, hgen⟩
    exact Pd28fa1e3B.forward_of D A T hT hgen (fun hS y => ⟨_, Pd28fa1e3B.res_gen hS y⟩)
  · rintro ⟨h1, h2, h3⟩
    exact Pd28fa1e3B.backward D A h1 h2 h3
