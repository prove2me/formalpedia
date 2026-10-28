-- Prove2me | solution 1 for EthierKurtz.hille_yosida_closed_dissipative_relation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:25:18.691542+00:00
-- url     : https://prove2.me/submissions/2b093467-9fc0-4047-b0e3-6e5bd543f442

import Mathlib
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

set_option autoImplicit false

open Filter
open scoped Topology

namespace Pd67abb68C1

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

end Pd67abb68C1

open Filter in
open scoped Topology in
/-- C1: Hille-Yosida generation for a closed dissipative (multivalued) linear relation. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (A : Submodule ℝ (E × E)) (hclosed : IsClosed (A : Set (E × E)))
    (hdiss : ∀ fg ∈ A, ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖)
    (hrange : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ h : E, ∀ delta : ℝ, 0 < delta →
      ∃ fg ∈ A, ‖(lam₀ • fg.1 - fg.2) - h‖ < delta)
    (hdense : ∀ h : E, ∀ delta : ℝ, 0 < delta → ∃ fg ∈ A, ‖fg.1 - h‖ < delta) :
    ∃ T : ℝ → E →L[ℝ] E,
      EthierKurtz.IsStronglyContinuousContractionSemigroup T ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A) := by
  exact Pd67abb68C1.hy_main hclosed hdiss hrange hdense
