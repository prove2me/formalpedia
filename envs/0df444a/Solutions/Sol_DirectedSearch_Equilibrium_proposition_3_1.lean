-- Prove2me | solution 1 for DirectedSearch.Equilibrium.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:55:00.876816+00:00
-- url     : https://prove2.me/submissions/ef174096-6814-457a-98d4-7248cc52c8a9

import Definitions.Def_DirectedSearch_Equilibrium_Setting

namespace DirectedSearch.Equilibrium

open MeasureTheory

noncomputable def Gf (μ : Measure ℝ) (t a : ℝ) : ℝ :=
  ∫ u, (Set.Ici a).indicator (fun u => min (t - u) 0) u ∂μ

noncomputable def gfun {ι : Type} [Fintype ι] (δ : ℝ) (lam : ι → ℝ) (F : ι → Measure ℝ)
    (x : ι → ℝ) (t : ℝ) : ℝ :=
  δ * t + ∑ i, lam i * Gf (F i) t (x i)

noncomputable def Kc (μ : Measure ℝ) : ℝ := ∫ u, min (0 - u) 0 ∂μ

lemma int_min (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) (t : ℝ) :
    Integrable (fun u => min (t - u) 0) μ := by
  have h1 : Integrable (fun u : ℝ => t - u) μ := (integrable_const t).sub hμ
  have h2 : Integrable (fun _ : ℝ => (0:ℝ)) μ := integrable_const 0
  exact h1.inf h2

lemma int_ind (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) (t a : ℝ) :
    Integrable ((Set.Ici a).indicator (fun u => min (t - u) 0)) μ :=
  (int_min μ hμ t).indicator measurableSet_Ici

lemma Gf_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) (t a : ℝ) :
    Gf μ t a = t * DirectedSearch.Approx.tailMass μ (max t a)
      - DirectedSearch.Approx.tailInt μ (max t a) := by
  have hpt : (Set.Ici a).indicator (fun u => min (t - u) 0)
      = (Set.Ici (max t a)).indicator (fun u => t - u) := by
    funext u
    by_cases h1 : a ≤ u <;> by_cases h2 : t ≤ u <;>
      simp [Set.indicator, h1, h2] <;> first | (intro h; linarith) | linarith | skip
  unfold Gf
  rw [hpt, integral_indicator measurableSet_Ici]
  have hid : Integrable (fun u : ℝ => u) μ := hμ
  rw [integral_sub (integrable_const t).integrableOn hid.integrableOn, setIntegral_const]
  simp [DirectedSearch.Approx.tailMass, DirectedSearch.Approx.tailInt, measureReal_def,
    mul_comm]

lemma Gf_mono_t (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) {t t' : ℝ}
    (h : t ≤ t') (a : ℝ) : Gf μ t a ≤ Gf μ t' a :=
  integral_mono (int_ind μ hμ t a) (int_ind μ hμ t' a)
    (fun u => Set.indicator_le_indicator (min_le_min_right 0 (by linarith)))

lemma Gf_mono_a (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) (t : ℝ) {a a' : ℝ}
    (h : a ≤ a') : Gf μ t a ≤ Gf μ t a' := by
  refine integral_mono (int_ind μ hμ t a) (int_ind μ hμ t a') (fun u => ?_)
  by_cases h1 : a ≤ u <;> by_cases h2 : a' ≤ u <;> simp [Set.indicator, h1, h2]
  all_goals first | linarith | exact min_le_right _ _ | skip

lemma Gf_max (μ : Measure ℝ) (t a : ℝ) : Gf μ t (max t a) = Gf μ t a := by
  unfold Gf
  congr 1
  funext u
  by_cases h1 : a ≤ u <;> by_cases h2 : t ≤ u <;> simp [Set.indicator, h1, h2]
  all_goals first | (intro h; linarith) | linarith | skip

lemma Gf_nonpos (μ : Measure ℝ) (t a : ℝ) : Gf μ t a ≤ 0 :=
  integral_nonpos (fun u => Set.indicator_nonpos (fun _ _ => min_le_right _ _) u)

lemma Kc_le (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) {t : ℝ} (ht : 0 ≤ t)
    (a : ℝ) : Kc μ ≤ Gf μ t a := by
  refine integral_mono (int_min μ hμ 0) (int_ind μ hμ t a) (fun u => ?_)
  by_cases h1 : a ≤ u <;> simp [Set.indicator, h1]
  all_goals first | exact Or.inl ht | (apply min_le_min_right; linarith) | exact min_le_right _ _ | skip

lemma Kc_nonpos (μ : Measure ℝ) : Kc μ ≤ 0 :=
  integral_nonpos (fun _ => min_le_right _ _)

lemma Gf_lip (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) (a t t' : ℝ) :
    |Gf μ t a - Gf μ t' a| ≤ |t - t'| * μ.real Set.univ := by
  unfold Gf
  rw [← integral_sub (int_ind μ hμ t a) (int_ind μ hμ t' a)]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun u => (Set.Ici a).indicator (fun u => min (t - u) 0) u
      - (Set.Ici a).indicator (fun u => min (t' - u) 0) u) (C := |t - t'|)
    (Filter.Eventually.of_forall (fun u => by
      by_cases h1 : a ≤ u <;> simp [Set.indicator, h1]
      have := abs_min_sub_min_le_max (t - u) 0 (t' - u) 0
      simpa using this))
  simpa using this

lemma Gf_cont (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) (a : ℝ) :
    Continuous (fun t => Gf μ t a) := by
  have hK : LipschitzWith (Real.toNNReal (μ.real Set.univ)) (fun t => Gf μ t a) := by
    refine LipschitzWith.of_dist_le_mul (fun t t' => ?_)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ measureReal_nonneg, mul_comm]
    exact Gf_lip μ hμ a t t'
  exact hK.continuous

section agent

variable {ι : Type} [Fintype ι] (δ : ℝ) (lam : ι → ℝ) (F : ι → Measure ℝ)

noncomputable def UB : ℝ := -(∑ i, lam i * Kc (F i)) / δ

noncomputable def root (x : ι → ℝ) : ℝ :=
  sSup {t | t ∈ Set.Icc 0 (UB δ lam F) ∧ gfun δ lam F x t ≤ 0}

variable {δ lam F} (hδ : 0 < δ) (hlam : ∀ i, 0 ≤ lam i) (hF : ∀ i, IsFiniteMeasure (F i))
  (hint : ∀ i, Integrable id (F i))
include hδ hlam hF hint

lemma UB_nonneg : 0 ≤ UB δ lam F := by
  unfold UB
  apply div_nonneg _ hδ.le
  rw [neg_nonneg]
  exact Finset.sum_nonpos (fun i _ => by
    have := Kc_nonpos (F i); have := hlam i; nlinarith)

lemma gfun_strictMono (x : ι → ℝ) : StrictMono (gfun δ lam F x) := by
  intro t t' h
  unfold gfun
  have : ∑ i, lam i * Gf (F i) t (x i) ≤ ∑ i, lam i * Gf (F i) t' (x i) :=
    Finset.sum_le_sum (fun i _ => by
      haveI := hF i
      exact mul_le_mul_of_nonneg_left (Gf_mono_t (F i) (hint i) h.le _) (hlam i))
  nlinarith

lemma gfun_mono_x {x y : ι → ℝ} (h : x ≤ y) (t : ℝ) : gfun δ lam F x t ≤ gfun δ lam F y t := by
  unfold gfun
  have : ∑ i, lam i * Gf (F i) t (x i) ≤ ∑ i, lam i * Gf (F i) t (y i) :=
    Finset.sum_le_sum (fun i _ => by
      haveI := hF i
      exact mul_le_mul_of_nonneg_left (Gf_mono_a (F i) (hint i) t (h i)) (hlam i))
  linarith

lemma gfun_zero (x : ι → ℝ) : gfun δ lam F x 0 ≤ 0 := by
  unfold gfun
  have : ∑ i, lam i * Gf (F i) 0 (x i) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => by
      have := Gf_nonpos (F i) 0 (x i); have := hlam i; nlinarith)
  linarith

lemma gfun_UB (x : ι → ℝ) : 0 ≤ gfun δ lam F x (UB δ lam F) := by
  unfold gfun
  have h0 := UB_nonneg hδ hlam hF hint
  have : ∑ i, lam i * Kc (F i) ≤ ∑ i, lam i * Gf (F i) (UB δ lam F) (x i) :=
    Finset.sum_le_sum (fun i _ => by
      haveI := hF i
      exact mul_le_mul_of_nonneg_left (Kc_le (F i) (hint i) h0 _) (hlam i))
  have hU : δ * UB δ lam F = -(∑ i, lam i * Kc (F i)) := by
    unfold UB; field_simp
  linarith

lemma gfun_cont (x : ι → ℝ) : Continuous (gfun δ lam F x) := by
  unfold gfun
  exact (continuous_const.mul continuous_id).add
    (continuous_finset_sum _ (fun i _ => by
      haveI := hF i
      exact continuous_const.mul (Gf_cont (F i) (hint i) (x i))))

lemma root_set_bdd (x : ι → ℝ) :
    BddAbove {t | t ∈ Set.Icc 0 (UB δ lam F) ∧ gfun δ lam F x t ≤ 0} :=
  ⟨UB δ lam F, fun _ ht => ht.1.2⟩

lemma root_set_ne (x : ι → ℝ) :
    ({t | t ∈ Set.Icc 0 (UB δ lam F) ∧ gfun δ lam F x t ≤ 0} : Set ℝ).Nonempty :=
  ⟨0, ⟨le_rfl, UB_nonneg hδ hlam hF hint⟩, gfun_zero hδ hlam hF hint x⟩

lemma root_mem (x : ι → ℝ) : root δ lam F x ∈ Set.Icc 0 (UB δ lam F) :=
  ⟨le_csSup (root_set_bdd hδ hlam hF hint x)
      ⟨⟨le_rfl, UB_nonneg hδ hlam hF hint⟩, gfun_zero hδ hlam hF hint x⟩,
    csSup_le (root_set_ne hδ hlam hF hint x) (fun _ ht => ht.1.2)⟩

lemma root_anti {x y : ι → ℝ} (h : x ≤ y) : root δ lam F y ≤ root δ lam F x :=
  csSup_le_csSup (root_set_bdd hδ hlam hF hint x) (root_set_ne hδ hlam hF hint y)
    (fun t ht => ⟨ht.1, (gfun_mono_x hδ hlam hF hint h t).trans ht.2⟩)

lemma root_spec (x : ι → ℝ) : gfun δ lam F x (root δ lam F x) = 0 := by
  have h0 := UB_nonneg hδ hlam hF hint
  obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc h0 (gfun_cont hδ hlam hF hint x).continuousOn
    ⟨gfun_zero hδ hlam hF hint x, gfun_UB hδ hlam hF hint x⟩
  have hsm := gfun_strictMono hδ hlam hF hint x
  have : root δ lam F x = c := by
    apply le_antisymm
    · apply csSup_le (root_set_ne hδ hlam hF hint x)
      intro t ht
      exact hsm.le_iff_le.1 (ht.2.trans hgc.ge)
    · exact le_csSup (root_set_bdd hδ hlam hF hint x) ⟨hc, hgc.le⟩
  rw [this, hgc]

lemma eq_iff (x : ι → ℝ) (t : ℝ) :
    t = ownU δ lam x F t ↔ gfun δ lam F x t = 0 := by
  have hD : 0 < δ + ∑ i, lam i * DirectedSearch.Approx.tailMass (F i) (max t (x i)) := by
    have : 0 ≤ ∑ i, lam i * DirectedSearch.Approx.tailMass (F i) (max t (x i)) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hlam i) ENNReal.toReal_nonneg)
    linarith
  have hg : gfun δ lam F x t = t * (δ + ∑ i, lam i *
      DirectedSearch.Approx.tailMass (F i) (max t (x i)))
      - ∑ i, lam i * DirectedSearch.Approx.tailInt (F i) (max t (x i)) := by
    unfold gfun
    have : ∑ i, lam i * Gf (F i) t (x i) = ∑ i, (t * (lam i *
        DirectedSearch.Approx.tailMass (F i) (max t (x i)))
        - lam i * DirectedSearch.Approx.tailInt (F i) (max t (x i))) := by
      apply Finset.sum_congr rfl
      intro i _
      haveI := hF i
      rw [Gf_eq (F i) (hint i)]
      ring
    rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  unfold ownU
  rw [hg, eq_div_iff hD.ne']
  constructor <;> intro h <;> linarith

lemma agent_unique {x y : ι → ℝ} {a b : ℝ} (hx : gfun δ lam F x a = 0)
    (hy : gfun δ lam F y b = 0) (hxy : ∀ i, x i ≠ y i → max (x i) (y i) ≤ max a b) :
    a = b := by
  have key : gfun δ lam F x (max a b) = gfun δ lam F y (max a b) := by
    unfold gfun
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i = y i
    · rw [hi]
    · have h := hxy i hi
      rw [← Gf_max (F i) _ (x i), ← Gf_max (F i) _ (y i),
        max_eq_left (le_trans (le_max_left _ _) h), max_eq_left (le_trans (le_max_right _ _) h)]
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    rw [max_eq_right hab.le] at key
    have := gfun_strictMono hδ hlam hF hint x hab
    linarith
  · exact hab
  · exfalso
    rw [max_eq_left hab.le] at key
    have := gfun_strictMono hδ hlam hF hint y hab
    linarith

end agent

theorem solution_aux {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (lamM : M → W → ℝ) (lamW : W → M → ℝ)
    (hlamM : ∀ m w, 0 ≤ lamM m w) (hlamW : ∀ w m, 0 ≤ lamW w m) :
    ∃! τ : (M → ℝ) × (W → ℝ),
      (∀ m, τ.1 m = uM mk lamM τ.1 τ.2 m) ∧ (∀ w, τ.2 w = uW mk lamW τ.1 τ.2 w) := by
  classical
  have hδ := hmk.delta_pos
  have hFM : ∀ m, ∀ w, IsFiniteMeasure (mk.F m w) := fun m w => by
    haveI := hmk.prob m w; infer_instance
  have hFW : ∀ w, ∀ m, IsFiniteMeasure ((fun m => mk.F m w) m) := fun w m => hFM m w
  have hiM : ∀ m, ∀ w, Integrable id (mk.F m w) := fun m w => hmk.integrable m w
  have hiW : ∀ w, ∀ m, Integrable id ((fun m => mk.F m w) m) := fun w m => hmk.integrable m w
  -- characterisation of the equations
  have eqM : ∀ (τ : (M → ℝ) × (W → ℝ)) m,
      τ.1 m = uM mk lamM τ.1 τ.2 m ↔ gfun mk.δ (lamM m) (mk.F m) τ.2 (τ.1 m) = 0 :=
    fun τ m => eq_iff hδ (hlamM m) (hFM m) (hiM m) τ.2 (τ.1 m)
  have eqW : ∀ (τ : (M → ℝ) × (W → ℝ)) w,
      τ.2 w = uW mk lamW τ.1 τ.2 w ↔
        gfun mk.δ (lamW w) (fun m => mk.F m w) τ.1 (τ.2 w) = 0 :=
    fun τ w => eq_iff hδ (hlamW w) (hFW w) (hiW w) τ.1 (τ.2 w)
  -- uniqueness
  have uniq : ∀ τ σ : (M → ℝ) × (W → ℝ),
      ((∀ m, τ.1 m = uM mk lamM τ.1 τ.2 m) ∧ (∀ w, τ.2 w = uW mk lamW τ.1 τ.2 w)) →
      ((∀ m, σ.1 m = uM mk lamM σ.1 σ.2 m) ∧ (∀ w, σ.2 w = uW mk lamW σ.1 σ.2 w)) →
      σ = τ := by
    intro τ σ hτ hσ
    let vt : M ⊕ W → ℝ := Sum.elim τ.1 τ.2
    let vs : M ⊕ W → ℝ := Sum.elim σ.1 σ.2
    let S := Finset.univ.filter (fun θ => vt θ ≠ vs θ)
    by_cases hS : S.Nonempty
    · exfalso
      obtain ⟨θ0, h0S, h0max⟩ := Finset.exists_max_image S (fun θ => max (vt θ) (vs θ)) hS
      have hbig : ∀ θ, vt θ ≠ vs θ → max (vt θ) (vs θ) ≤ max (vt θ0) (vs θ0) :=
        fun θ h => h0max θ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      have h0ne : vt θ0 ≠ vs θ0 := (Finset.mem_filter.1 h0S).2
      rcases θ0 with m | w
      · apply h0ne
        exact agent_unique hδ (hlamM m) (hFM m) (hiM m) ((eqM τ m).1 (hτ.1 m))
          ((eqM σ m).1 (hσ.1 m)) (fun w hw => hbig (Sum.inr w) hw)
      · apply h0ne
        exact agent_unique hδ (hlamW w) (hFW w) (hiW w) ((eqW τ w).1 (hτ.2 w))
          ((eqW σ w).1 (hσ.2 w)) (fun m hm => hbig (Sum.inl m) hm)
    · have hall : ∀ θ, vt θ = vs θ := by
        intro θ
        by_contra h
        exact hS ⟨θ, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
      ext m
      · exact (hall (Sum.inl m)).symm
      · exact (hall (Sum.inr m)).symm
  -- existence via Knaster–Tarski
  let UBM : M → ℝ := fun m => UB mk.δ (lamM m) (mk.F m)
  let UBW : W → ℝ := fun w => UB mk.δ (lamW w) (fun m => mk.F m w)
  let lo : M ⊕ W → ℝ := Sum.elim 0 (fun w => -UBW w)
  let hi : M ⊕ W → ℝ := Sum.elim UBM 0
  have hlohi : lo ≤ hi := by
    intro θ
    rcases θ with m | w
    · exact UB_nonneg hδ (hlamM m) (hFM m) (hiM m)
    · show -UBW w ≤ 0
      exact neg_nonpos.2 (UB_nonneg hδ (hlamW w) (hFW w) (hiW w))
  haveI : Fact (lo ≤ hi) := ⟨hlohi⟩
  let rM : M → (W → ℝ) → ℝ := fun m x => root mk.δ (lamM m) (mk.F m) x
  let rW : W → (M → ℝ) → ℝ := fun w x => root mk.δ (lamW w) (fun m => mk.F m w) x
  let A : (M ⊕ W → ℝ) → (M → ℝ) := fun z m => z (Sum.inl m)
  let B : (M ⊕ W → ℝ) → (W → ℝ) := fun z w => -z (Sum.inr w)
  let f : (M ⊕ W → ℝ) → (M ⊕ W → ℝ) := fun z =>
    Sum.elim (fun m => rM m (B z)) (fun w => -(rW w (A z)))
  have hfmem : ∀ z, f z ∈ Set.Icc lo hi := by
    intro z
    refine ⟨fun θ => ?_, fun θ => ?_⟩ <;> rcases θ with m | w
    · exact (root_mem hδ (hlamM m) (hFM m) (hiM m) _).1
    · exact neg_le_neg (root_mem hδ (hlamW w) (hFW w) (hiW w) _).2
    · exact (root_mem hδ (hlamM m) (hFM m) (hiM m) _).2
    · exact neg_nonpos.2 (root_mem hδ (hlamW w) (hFW w) (hiW w) _).1
  have hfmono : Monotone f := by
    intro z z' hz θ
    rcases θ with m | w
    · exact root_anti hδ (hlamM m) (hFM m) (hiM m) (fun w => neg_le_neg (hz (Sum.inr w)))
    · exact neg_le_neg (root_anti hδ (hlamW w) (hFW w) (hiW w) (fun m => hz (Sum.inl m)))
  let Φ : Set.Icc lo hi →o Set.Icc lo hi :=
    { toFun := fun p => ⟨f p.1, hfmem p.1⟩
      monotone' := fun p q hpq => hfmono hpq }
  let p := OrderHom.lfp Φ
  have hp : Φ p = p := Φ.map_lfp
  have hpf : f p.1 = p.1 := congrArg Subtype.val hp
  have hp1 : ∀ m, A p.1 m = rM m (B p.1) := fun m => (congrFun hpf (Sum.inl m)).symm
  have hp2 : ∀ w, B p.1 w = rW w (A p.1) := fun w => by
    have := congrFun hpf (Sum.inr w)
    show -p.1 (Sum.inr w) = _
    rw [← this]
    exact neg_neg _
  let τ : (M → ℝ) × (W → ℝ) := (A p.1, B p.1)
  have hτ : (∀ m, τ.1 m = uM mk lamM τ.1 τ.2 m) ∧ (∀ w, τ.2 w = uW mk lamW τ.1 τ.2 w) := by
    refine ⟨fun m => (eqM τ m).2 ?_, fun w => (eqW τ w).2 ?_⟩
    · show gfun mk.δ (lamM m) (mk.F m) (B p.1) (A p.1 m) = 0
      rw [hp1 m]
      exact root_spec hδ (hlamM m) (hFM m) (hiM m) _
    · show gfun mk.δ (lamW w) (fun m => mk.F m w) (A p.1) (B p.1 w) = 0
      rw [hp2 w]
      exact root_spec hδ (hlamW w) (hFW w) (hiW w) _
  exact ⟨τ, hτ, fun σ hσ => uniq τ σ hτ hσ⟩

theorem proposition_3_1 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (lamM : M → W → ℝ) (lamW : W → M → ℝ)
    (hlamM : ∀ m w, 0 ≤ lamM m w) (hlamW : ∀ w m, 0 ≤ lamW w m) :
    ∃! τ : (M → ℝ) × (W → ℝ),
      (∀ m, τ.1 m = uM mk lamM τ.1 τ.2 m) ∧ (∀ w, τ.2 w = uW mk lamW τ.1 τ.2 w) :=
  solution_aux mk hmk lamM lamW hlamM hlamW

theorem _root_.solution {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (lamM : M → W → ℝ) (lamW : W → M → ℝ)
    (hlamM : ∀ m w, 0 ≤ lamM m w) (hlamW : ∀ w m, 0 ≤ lamW w m) :
    ∃! τ : (M → ℝ) × (W → ℝ),
      (∀ m, τ.1 m = uM mk lamM τ.1 τ.2 m) ∧ (∀ w, τ.2 w = uW mk lamW τ.1 τ.2 w) :=
  solution_aux mk hmk lamM lamW hlamM hlamW

end DirectedSearch.Equilibrium
