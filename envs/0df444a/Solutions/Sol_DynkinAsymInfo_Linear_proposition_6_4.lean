-- Prove2me | solution 1 for DynkinAsymInfo.Linear.proposition_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T10:11:35.421562+00:00
-- url     : https://prove2.me/submissions/9c468b65-bd28-48b3-8808-6cd23bb65102

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal


namespace DynkinRunMax

variable (f : ℝ≥0 → ℝ)

lemma bdd (hf : Continuous f) (t : ℝ≥0) : BddAbove (f '' Set.Icc 0 t) :=
  (isCompact_Icc.image hf).bddAbove

lemma ne (t : ℝ≥0) : (f '' Set.Icc 0 t).Nonempty := ⟨f 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩

lemma le_M (hf : Continuous f) {s t : ℝ≥0} (hst : s ≤ t) : f s ≤ sSup (f '' Set.Icc 0 t) :=
  le_csSup (bdd f hf t) ⟨s, ⟨zero_le, hst⟩, rfl⟩

lemma M_mono (hf : Continuous f) : Monotone (fun t => sSup (f '' Set.Icc 0 t)) := by
  intro s t hst
  exact csSup_le_csSup (bdd f hf t) (ne f s)
    (Set.image_mono (Set.Icc_subset_Icc le_rfl hst))

lemma M_zero : sSup (f '' Set.Icc 0 0) = f 0 := by
  rw [Set.Icc_self, Set.image_singleton, csSup_singleton]

lemma image_eq (t : ℝ≥0) :
    f '' Set.Icc 0 t = (fun s : ℝ≥0 => f (s * t)) '' Set.Icc 0 1 := by
  ext y; constructor
  · rintro ⟨u, hu, rfl⟩
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      have : u = 0 := le_antisymm hu.2 (zero_le)
      subst this
      exact ⟨0, ⟨le_rfl, zero_le⟩, by simp⟩
    · refine ⟨u / t, ⟨zero_le, ?_⟩, ?_⟩
      · rw [div_le_one (pos_iff_ne_zero.mpr ht)]; exact hu.2
      · simp only; rw [div_mul_cancel₀ u ht]
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s * t, ⟨zero_le, mul_le_of_le_one_left (zero_le) hs.2⟩, rfl⟩

lemma M_cont (hf : Continuous f) : Continuous (fun t => sSup (f '' Set.Icc 0 t)) := by
  have : (fun t => sSup (f '' Set.Icc 0 t)) =
      fun t => sSup ((fun t (s : ℝ≥0) => f (s * t)) t '' Set.Icc 0 1) := by
    funext t; rw [image_eq]
  rw [this]
  apply isCompact_Icc.continuous_sSup
  exact hf.comp (continuous_snd.mul continuous_fst)

/-- the running max is attained at a point after `s` if it strictly increased -/
lemma attained (hf : Continuous f) {s t : ℝ≥0}
    (hlt : sSup (f '' Set.Icc 0 s) < sSup (f '' Set.Icc 0 t)) :
    ∃ u, s < u ∧ u ≤ t ∧ f u = sSup (f '' Set.Icc 0 t) ∧
      sSup (f '' Set.Icc 0 u) = sSup (f '' Set.Icc 0 t) := by
  obtain ⟨u, hu, hfu⟩ := (isCompact_Icc.image hf).sSup_mem (ne f t)
  have hsu : s < u := by
    by_contra h; push Not at h
    have := le_M f hf h
    rw [hfu] at this; linarith
  refine ⟨u, hsu, hu.2, hfu, le_antisymm ?_ ?_⟩
  · exact M_mono f hf hu.2
  · rw [← hfu]; exact le_M f hf le_rfl

/-- countable test set -/
def D (t : ℝ≥0) : Set ℝ := {0} ∪ (Set.Ioo 0 (t : ℝ) ∩ Set.range ((↑) : ℚ → ℝ))

lemma D_countable (t : ℝ≥0) : (D t).Countable :=
  (Set.countable_singleton 0).union ((Set.countable_range _).mono Set.inter_subset_right)

lemma D_sub (t : ℝ≥0) : D t ⊆ Set.Icc 0 (t : ℝ) := by
  rintro q (hq | hq)
  · rw [Set.mem_singleton_iff.mp hq]; exact ⟨le_rfl, t.2⟩
  · exact ⟨hq.1.1.le, hq.1.2.le⟩

lemma Icc_sub_closure (t : ℝ≥0) : Set.Icc 0 (t : ℝ) ⊆ closure (D t) := by
  rcases eq_or_lt_of_le t.2 with h | h
  · intro q hq
    have : q = 0 := le_antisymm (h ▸ hq.2) hq.1
    exact subset_closure (Or.inl this)
  · calc Set.Icc 0 (t : ℝ) = closure (Set.Ioo 0 (t : ℝ)) := (closure_Ioo h.ne).symm
      _ ⊆ closure (closure (Set.Ioo 0 (t : ℝ) ∩ Set.range ((↑) : ℚ → ℝ))) :=
          closure_mono (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
      _ = closure (Set.Ioo 0 (t : ℝ) ∩ Set.range ((↑) : ℚ → ℝ)) := closure_closure
      _ ⊆ closure (D t) := closure_mono Set.subset_union_right

lemma M_le_iff (hf : Continuous f) (t : ℝ≥0) (c : ℝ) :
    sSup (f '' Set.Icc 0 t) ≤ c ↔ ∀ q ∈ D t, f (Real.toNNReal q) ≤ c := by
  rw [csSup_le_iff (bdd f hf t) (ne f t)]
  constructor
  · intro h q hq
    have hq' := D_sub t hq
    apply h
    refine ⟨Real.toNNReal q, ⟨zero_le, ?_⟩, rfl⟩
    rw [Real.toNNReal_le_iff_le_coe]; exact hq'.2
  · intro h y hy
    obtain ⟨u, hu, rfl⟩ := hy
    have hg : Continuous (fun r : ℝ => f (Real.toNNReal r)) :=
      hf.comp continuous_real_toNNReal
    have hcl : IsClosed {r : ℝ | f (Real.toNNReal r) ≤ c} := isClosed_le hg continuous_const
    have hsub : closure (D t) ⊆ {r : ℝ | f (Real.toNNReal r) ≤ c} :=
      closure_minimal (fun q hq => h q hq) hcl
    have hu' : (u : ℝ) ∈ Set.Icc 0 (t : ℝ) := ⟨u.2, by exact_mod_cast hu.2⟩
    have := hsub (Icc_sub_closure t hu')
    simpa using this

lemma measurable_M {Ω : Type*} (m : MeasurableSpace Ω) (F : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (hF : ∀ s ≤ t, Measurable[m] (F s)) (hc : ∀ a, Continuous (fun s => F s a)) :
    Measurable[m] (fun a => sSup ((fun s => F s a) '' Set.Icc 0 t)) := by
  let _ := m
  apply measurable_of_Iic
  intro c
  have : (fun a => sSup ((fun s => F s a) '' Set.Icc 0 t)) ⁻¹' Set.Iic c =
      ⋂ q ∈ D t, {a | F (Real.toNNReal q) a ≤ c} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
    exact M_le_iff (fun s => F s a) (hc a) t c
  rw [this]
  refine MeasurableSet.biInter (D_countable t) (fun q hq => ?_)
  have hq' := D_sub t hq
  have : Real.toNNReal q ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hq'.2
  exact measurableSet_le (hF _ this) measurable_const

end DynkinRunMax

namespace DynkinRunMax

theorem pathwise (f : ℝ≥0 → ℝ) (hf : Continuous f) (hpos : ∀ t, 0 < f t)
    (phi B : ℝ) (hphi : f 0 = phi) (hB : 0 < B) :
    let M := fun t => sSup (f '' Set.Icc 0 t)
    let G := fun t => max 0 (1 - B / M t)
    let PB := fun t => f t * (1 - G t)
    let R := fun t => -B * Real.log ((1 - G t) / (1 - G 0))
    (Continuous R ∧ Monotone R ∧ R 0 = 0 ∧ PB 0 = min phi B ∧
      (∀ t, 0 < PB t ∧ PB t ≤ B) ∧
      (∀ s t, s ≤ t → (∀ u ∈ Set.Icc s t, PB u < B) → R s = R t) ∧
      (∀ t, PB t = min phi B * (f t / phi) * Real.exp (-R t / B)) ∧
      G 0 = max 0 (1 - B / phi) ∧ (∀ t, G t < 1)) ∧
    (Monotone G ∧ (∀ t, ContinuousWithinAt G (Set.Ici t) t) ∧ 0 ≤ G 0 ∧ ∀ t, G t ≤ 1) := by
  intro M G PB R
  have hphi0 : 0 < phi := hphi ▸ hpos 0
  have hMpos : ∀ t, 0 < M t := fun t => lt_of_lt_of_le (hpos t) (le_M f hf le_rfl)
  have hfM : ∀ t, f t ≤ M t := fun t => le_M f hf le_rfl
  have hMmono : Monotone M := M_mono f hf
  have hMcont : Continuous M := M_cont f hf
  have hM0 : M 0 = phi := by show sSup (f '' Set.Icc 0 0) = phi; rw [M_zero, hphi]
  set E := fun t => max (M t) B with hE
  have hEpos : ∀ t, 0 < E t := fun t => lt_of_lt_of_le hB (le_max_right _ _)
  have hG1 : ∀ t, 1 - G t = B / E t := by
    intro t
    show 1 - max 0 (1 - B / M t) = B / max (M t) B
    rcases le_total (M t) B with h | h
    · rw [max_eq_right h, div_self hB.ne']
      have : 1 ≤ B / M t := by rw [le_div_iff₀ (hMpos t)]; linarith
      rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_left h]
      have : B / M t ≤ 1 := by rw [div_le_iff₀ (hMpos t)]; linarith
      rw [max_eq_right (by linarith)]; ring
  have hR : ∀ t, R t = B * (Real.log (E t) - Real.log (E 0)) := by
    intro t
    show -B * Real.log ((1 - G t) / (1 - G 0)) = _
    rw [hG1, hG1]
    have : B / E t / (B / E 0) = E 0 / E t := by
      field_simp [(hEpos t).ne', (hEpos 0).ne', hB.ne']
    rw [this, Real.log_div (hEpos 0).ne' (hEpos t).ne']; ring
  have hPB : ∀ t, PB t = f t * B / E t := by
    intro t; show f t * (1 - G t) = _; rw [hG1]; ring
  have hEmono : Monotone E := fun s t hst => max_le_max (hMmono hst) le_rfl
  have hEcont : Continuous E := hMcont.max continuous_const
  have hE0 : E 0 = max phi B := by show max (M 0) B = _; rw [hM0]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have : R = fun t => B * (Real.log (E t) - Real.log (E 0)) := funext hR
    rw [this]
    exact continuous_const.mul ((hEcont.log fun t => (hEpos t).ne').sub continuous_const)
  · intro s t hst
    rw [hR, hR]
    have := Real.log_le_log (hEpos s) (hEmono hst)
    nlinarith
  · rw [hR]; ring
  · rw [hPB, hphi, hE0]
    rcases le_total phi B with h | h
    · rw [max_eq_right h, min_eq_left h]; field_simp
    · rw [max_eq_left h, min_eq_right h]; field_simp
  · intro t
    rw [hPB]
    refine ⟨div_pos (mul_pos (hpos t) hB) (hEpos t), ?_⟩
    rw [div_le_iff₀ (hEpos t)]
    have : f t ≤ E t := le_trans (hfM t) (le_max_left _ _)
    nlinarith
  · intro s t hst hflat
    rw [hR, hR]
    by_contra hne
    have hEne : E s ≠ E t := by
      intro h; apply hne; rw [h]
    have hlt : E s < E t := lt_of_le_of_ne (hEmono hst) hEne
    have hMt : E t = M t := by
      show max (M t) B = M t
      apply max_eq_left
      by_contra h; push Not at h
      have : E t = B := max_eq_right h.le
      have : B ≤ E s := le_max_right _ _
      linarith
    have hMlt : M s < M t := by
      have : M s ≤ E s := le_max_left _ _
      linarith
    obtain ⟨u, hsu, hut, hfu, hMu⟩ := attained f hf hMlt
    have hBMt : B ≤ M t := by
      have := le_max_right (M t) B
      have h2 : E t = max (M t) B := rfl
      rw [← h2, hMt] at this; exact this
    have hEu : E u = M t := by
      show max (M u) B = M t
      have hMu' : M u = M t := hMu
      rw [hMu']; exact max_eq_left hBMt
    have hfu' : f u = M t := hfu
    have := hflat u ⟨hsu.le, hut⟩
    rw [hPB, hEu, hfu'] at this
    have h3 : M t * B / M t = B := by field_simp [(hMpos t).ne']
    linarith
  · intro t
    rw [hPB, hR]
    have : -(B * (Real.log (E t) - Real.log (E 0))) / B = Real.log (E 0) - Real.log (E t) := by
      field_simp; ring
    rw [this, Real.exp_sub, Real.exp_log (hEpos 0), Real.exp_log (hEpos t), hE0]
    have hmm : min phi B * max phi B = phi * B := min_mul_max phi B
    field_simp [(hEpos t).ne']
    linear_combination (-(f t)) * hmm
  · show max 0 (1 - B / M 0) = _; rw [hM0]
  · intro t
    show max 0 (1 - B / M t) < 1
    have : 0 < B / M t := div_pos hB (hMpos t)
    exact max_lt one_pos (by linarith)
  · intro s t hst
    show max 0 (1 - B / M s) ≤ max 0 (1 - B / M t)
    apply max_le_max le_rfl
    have : B / M t ≤ B / M s := div_le_div_of_nonneg_left hB.le (hMpos s) (hMmono hst)
    linarith
  · intro t
    have : Continuous G :=
      continuous_const.max (continuous_const.sub (continuous_const.div hMcont
        (fun t => (hMpos t).ne')))
    exact this.continuousAt.continuousWithinAt
  · exact le_max_left _ _
  · intro t
    show max 0 (1 - B / M t) ≤ 1
    have : 0 < B / M t := div_pos hB (hMpos t)
    exact max_le zero_le_one (by linarith)

end DynkinRunMax



namespace DynkinRunMax
open DynkinAsymInfo.Linear

variable {Ω : Type*} [MeasurableSpace Ω]

lemma X_pos (p : Params) (st : Setting Ω) (x pi : ℝ) (hx : 0 < x) (t : ℝ≥0) (a : Ω) :
    0 < X p st x pi t a := by
  unfold X; positivity

lemma X_cont (p : Params) (st : Setting Ω) (x pi : ℝ) (a : Ω) :
    Continuous (fun t => X p st x pi t a) := by
  unfold X
  have hW := st.continuous_W a
  fun_prop

lemma Phi_cont (p : Params) (st : Setting Ω) (x pi : ℝ) (hx : 0 < x) (a : Ω) :
    Continuous (fun t => Phi p st x pi t a) := by
  unfold Phi
  have hX := X_cont p st x pi a
  have hlog : Continuous (fun t => Real.log (X p st x pi t a / x)) :=
    (hX.div_const x).log (fun t => (div_pos (X_pos p st x pi hx t a) hx).ne')
  fun_prop

lemma Phi_pos (p : Params) (st : Setting Ω) (x pi : ℝ) (hpi : pi ∈ Set.Ioo 0 1)
    (t : ℝ≥0) (a : Ω) : 0 < Phi p st x pi t a := by
  unfold Phi
  have : 0 < pi / (1 - pi) := div_pos hpi.1 (by linarith [hpi.2])
  positivity

lemma Phi_meas (p : Params) (st : Setting Ω) (x pi : ℝ) (s : ℝ≥0) :
    Measurable[MeasurableSpace.comap (X p st x pi s) (inferInstance : MeasurableSpace ℝ)]
      (Phi p st x pi s) := by
  have hg : Measurable (fun y : ℝ => pi / (1 - pi) * Real.exp ((signalNoise p / p.sigma) *
      (Real.log (y / x) - (p.mu0 - p.sigma ^ 2 / 2) * (s : ℝ)) -
      signalNoise p ^ 2 * (s : ℝ) / 2)) := by
    fun_prop
  exact hg.comp (comap_measurable (X p st x pi s))

lemma comap_le_FX (p : Params) (st : Setting Ω) (x pi : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    MeasurableSpace.comap (X p st x pi s) (inferInstance : MeasurableSpace ℝ) ≤
      FX p st x pi t := by
  intro A hA
  have h1 : MeasurableSet[⨆ (u : ℝ≥0) (_ : u ≤ t),
      MeasurableSpace.comap (X p st x pi u) (inferInstance : MeasurableSpace ℝ)] A :=
    (le_iSup₂ (f := fun (u : ℝ≥0) (_ : u ≤ t) =>
      MeasurableSpace.comap (X p st x pi u) (inferInstance : MeasurableSpace ℝ)) s hst) A hA
  exact MeasurableSpace.measurableSet_generateFrom (Or.inl h1)

lemma Phi_zero (p : Params) (st : Setting Ω) (x pi : ℝ) (hx : 0 < x) (a : Ω)
    (hW0 : st.W 0 a = 0) : Phi p st x pi 0 a = pi / (1 - pi) := by
  unfold Phi X
  simp [hW0, hx.ne']

end DynkinRunMax

open DynkinAsymInfo.Linear in
theorem p64_main {Ω : Type*} [MeasurableSpace Ω] (p : Params)
    (st : Setting Ω) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (x pi B : ℝ) (hx : 0 < x) (hpi : pi ∈ Set.Ioo 0 1)
    (hB : 0 < B) :
    let phi := pi / (1 - pi)
    InA st (FX p st x pi) (GammaB p st x pi B) ∧
    (∀ᵐ a ∂st.P,
      Continuous (fun t => regulatorB p st x pi B t a) ∧
      Monotone (fun t => regulatorB p st x pi B t a) ∧
      regulatorB p st x pi B 0 a = 0 ∧
      PhiB p st x pi B 0 a = min phi B ∧
      (∀ t, 0 < PhiB p st x pi B t a ∧ PhiB p st x pi B t a ≤ B) ∧
      (∀ s t, s ≤ t →
        (∀ u ∈ Set.Icc s t, PhiB p st x pi B u a < B) →
        regulatorB p st x pi B s a = regulatorB p st x pi B t a) ∧
      (∀ t, PhiB p st x pi B t a =
        min phi B * (Phi p st x pi t a / phi) *
          Real.exp (-regulatorB p st x pi B t a / B)) ∧
      GammaB p st x pi B 0 a = max 0 (1 - B / phi) ∧
      (∀ t, GammaB p st x pi B t a < 1)) := by
  intro phi
  have hW0 : ∀ᵐ a ∂st.P, st.W 0 a = 0 := st.brownian.eval_zero_ae_eq_zero
  have hpath : ∀ a, st.W 0 a = 0 → _ := fun a ha =>
    DynkinRunMax.pathwise (fun t => Phi p st x pi t a) (DynkinRunMax.Phi_cont p st x pi hx a)
      (fun t => DynkinRunMax.Phi_pos p st x pi hpi t a) phi B
      (DynkinRunMax.Phi_zero p st x pi hx a ha) hB
  refine ⟨⟨fun t => ?_, ?_⟩, ?_⟩
  · -- measurability
    have hM : Measurable[FX p st x pi t] (fun a => runMax p st x pi t a) := by
      apply DynkinRunMax.measurable_M (FX p st x pi t) (fun s a => Phi p st x pi s a) t
      · intro s hs
        exact (DynkinRunMax.Phi_meas p st x pi s).mono (DynkinRunMax.comap_le_FX p st x pi hs)
          le_rfl
      · intro a; exact DynkinRunMax.Phi_cont p st x pi hx a
    show Measurable[FX p st x pi t] (fun a => max 0 (1 - B / runMax p st x pi t a))
    let _ : MeasurableSpace Ω := FX p st x pi t
    exact measurable_const.max (measurable_const.sub (measurable_const.div hM))
  · filter_upwards [hW0] with a ha
    exact (hpath a ha).2
  · filter_upwards [hW0] with a ha
    exact (hpath a ha).1


open DynkinAsymInfo.Linear in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params)
    (st : Setting Ω) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (x pi B : ℝ) (hx : 0 < x) (hpi : pi ∈ Set.Ioo 0 1)
    (hB : 0 < B) :
    let phi := pi / (1 - pi)
    InA st (FX p st x pi) (GammaB p st x pi B) ∧
    (∀ᵐ a ∂st.P,
      Continuous (fun t => regulatorB p st x pi B t a) ∧
      Monotone (fun t => regulatorB p st x pi B t a) ∧
      regulatorB p st x pi B 0 a = 0 ∧
      PhiB p st x pi B 0 a = min phi B ∧
      (∀ t, 0 < PhiB p st x pi B t a ∧ PhiB p st x pi B t a ≤ B) ∧
      (∀ s t, s ≤ t →
        (∀ u ∈ Set.Icc s t, PhiB p st x pi B u a < B) →
        regulatorB p st x pi B s a = regulatorB p st x pi B t a) ∧
      (∀ t, PhiB p st x pi B t a =
        min phi B * (Phi p st x pi t a / phi) *
          Real.exp (-regulatorB p st x pi B t a / B)) ∧
      GammaB p st x pi B 0 a = max 0 (1 - B / phi) ∧
      (∀ t, GammaB p st x pi B t a < 1)) :=
  p64_main p st h62 x pi B hx hpi hB
