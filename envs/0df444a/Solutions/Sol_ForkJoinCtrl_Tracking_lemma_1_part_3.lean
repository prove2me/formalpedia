-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.lemma_1_part_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:51:52.755188+00:00
-- url     : https://prove2.me/submissions/9aca1342-0b00-4d79-99a6-07efcb9ade9f

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP
import Theorems.Thm_ForkJoinCtrl_Tracking_lemma_1_part_2


open Filter Topology

namespace FJPolyProj

variable {ι L : Type*} [Fintype ι] [Fintype L]

def dot (u v : ι → ℝ) : ℝ := ∑ c, u c * v c

theorem dot_add_right (u v w : ι → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_sub_right (u v w : ι → ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dot_smul_right (u v : ι → ℝ) (c : ℝ) : dot u (c • v) = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl
  intro i _; ring

theorem dot_comm (u v : ι → ℝ) : dot u v = dot v u := by
  simp only [dot]; apply Finset.sum_congr rfl; intro i _; ring

theorem dot_self_nonneg (u : ι → ℝ) : 0 ≤ dot u u :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

theorem dot_self_eq_zero {u : ι → ℝ} (h : dot u u = 0) : u = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (u i))).1 h
  funext i; simpa using this i (Finset.mem_univ i)

theorem sq_le_dot_self (u : ι → ℝ) (i : ι) : u i * u i ≤ dot u u :=
  Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i))
    (Finset.mem_univ i)

theorem continuous_dot_left (u : ι → ℝ) : Continuous (fun v : ι → ℝ => dot u v) := by
  unfold dot; fun_prop

theorem continuous_dot_self : Continuous (fun v : ι → ℝ => dot v v) := by
  unfold dot; fun_prop

/-- expansion of the square -/
theorem dot_expand (x d : ι → ℝ) (e : ℝ) :
    dot (x + e • d) (x + e • d) = dot x x + 2 * e * dot x d + e ^ 2 * dot d d := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

variable (a : L → ι → ℝ)

def Feas (β : L → ℝ) (x : ι → ℝ) : Prop := ∀ l, dot (a l) x ≤ β l

def IsMinNorm (β : L → ℝ) (x : ι → ℝ) : Prop :=
  Feas a β x ∧ ∀ y, Feas a β y → dot x x ≤ dot y y

variable {a}

theorem feas_comb {β1 β2 : L → ℝ} {x1 x2 : ι → ℝ} (h1 : Feas a β1 x1) (h2 : Feas a β2 x2)
    (θ : ℝ) (h0 : 0 ≤ θ) (h1' : θ ≤ 1) :
    Feas a ((1 - θ) • β1 + θ • β2) ((1 - θ) • x1 + θ • x2) := by
  intro l
  rw [dot_add_right, dot_smul_right, dot_smul_right]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := h1 l; have := h2 l
  nlinarith

theorem dot_comb_le (x1 x2 : ι → ℝ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    dot ((1 - θ) • x1 + θ • x2) ((1 - θ) • x1 + θ • x2) ≤ (1 - θ) * dot x1 x1 + θ * dot x2 x2 := by
  have key : dot ((1 - θ) • x1 + θ • x2) ((1 - θ) • x1 + θ • x2) =
      (1 - θ) * dot x1 x1 + θ * dot x2 x2 - θ * (1 - θ) * dot (x1 - x2) (x1 - x2) := by
    simp only [dot, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [key]
  have := dot_self_nonneg (x1 - x2)
  have : 0 ≤ θ * (1 - θ) := mul_nonneg h0 (by linarith)
  nlinarith

/-- variational inequality -/
theorem vi {β : L → ℝ} {x : ι → ℝ} (hx : IsMinNorm a β x) {y : ι → ℝ} (hy : Feas a β y) :
    0 ≤ dot x (y - x) := by
  by_contra hneg
  push Not at hneg
  set c := dot x (y - x)
  set D := dot (y - x) (y - x)
  have hD := dot_self_nonneg (y - x)
  set e := min 1 (-c / (D + 1)) with he
  have he0 : 0 < e := lt_min one_pos (div_pos (by linarith) (by linarith))
  have he1 : e ≤ 1 := min_le_left _ _
  have hfe : Feas a β (x + e • (y - x)) := by
    have := feas_comb hx.1 hy e he0.le he1
    have e1 : (1 - e) • β + e • β = β := by
      funext l; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : (1 - e) • x + e • y = x + e • (y - x) := by
      funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rwa [e1, e2] at this
  have := hx.2 _ hfe
  rw [dot_expand] at this
  have h2 : e * D ≤ -c * D / (D + 1) := by
    have : e ≤ -c / (D + 1) := min_le_right _ _
    calc e * D ≤ (-c / (D + 1)) * D := mul_le_mul_of_nonneg_right this hD
      _ = -c * D / (D + 1) := by ring
  have h3 : -c * D / (D + 1) < -c := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have : 0 ≤ 2 * c + e * D := by nlinarith
  linarith

theorem minNorm_unique {β : L → ℝ} {x x' : ι → ℝ} (hx : IsMinNorm a β x)
    (hx' : IsMinNorm a β x') : x = x' := by
  have h1 := vi hx hx'.1
  have h2 := vi hx' hx.1
  have : dot (x - x') (x - x') = -(dot x (x' - x) + dot x' (x - x')) := by
    simp only [dot, Pi.sub_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have h3 : dot (x - x') (x - x') = 0 := by
    have := dot_self_nonneg (x - x'); linarith
  exact sub_eq_zero.1 (dot_self_eq_zero h3)

theorem isClosed_feas (β : L → ℝ) : IsClosed {x | Feas a β x} := by
  have : {x | Feas a β x} = ⋂ l, {x | dot (a l) x ≤ β l} := by
    ext x; simp [Feas]
  rw [this]
  exact isClosed_iInter (fun l => isClosed_le (continuous_dot_left _) continuous_const)

theorem minNorm_exists {β : L → ℝ} {x0 : ι → ℝ} (h0 : Feas a β x0) : ∃ x, IsMinNorm a β x := by
  set R := dot x0 x0
  set C := {x | Feas a β x} ∩ {x : ι → ℝ | dot x x ≤ R}
  have hCc : IsClosed C :=
    (isClosed_feas β).inter (isClosed_le continuous_dot_self continuous_const)
  have hCb : Bornology.IsBounded C := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt R, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    have := sq_le_dot_self x i
    have h2 : dot x x ≤ R := hx.2
    rw [sq]; linarith
  have hCk : IsCompact C := Metric.isCompact_of_isClosed_isBounded hCc hCb
  obtain ⟨x, hxC, hmin⟩ := hCk.exists_isMinOn ⟨x0, h0, show dot x0 x0 ≤ R from le_refl _⟩
    continuous_dot_self.continuousOn
  refine ⟨x, hxC.1, fun y hy => ?_⟩
  by_cases hyR : dot y y ≤ R
  · exact hmin ⟨hy, hyR⟩
  · push Not at hyR
    have : dot x x ≤ R := hxC.2
    linarith

/-- the kernel-orthogonality of the min-norm point w.r.t. its active constraints -/
theorem active_orth {β : L → ℝ} {x : ι → ℝ} (hx : IsMinNorm a β x) (k : ι → ℝ)
    (hk : ∀ l, dot (a l) x = β l → dot (a l) k = 0) : dot x k = 0 := by
  have hev : ∀ᶠ e in 𝓝 (0 : ℝ), Feas a β (x + e • k) := by
    show ∀ᶠ e in 𝓝 (0 : ℝ), ∀ l, dot (a l) (x + e • k) ≤ β l
    simp only [eventually_all]
    intro l
    by_cases hl : dot (a l) x = β l
    · refine Eventually.of_forall (fun e => ?_)
      rw [dot_add_right, dot_smul_right, hk l hl]; simp [hl]
    · have hlt : dot (a l) x < β l := lt_of_le_of_ne (hx.1 l) hl
      have hc : Continuous (fun e : ℝ => dot (a l) (x + e • k)) := by
        simp only [dot_add_right, dot_smul_right]; fun_prop
      have := hc.continuousAt (x := 0) |>.eventually (gt_mem_nhds (show dot (a l) (x + (0:ℝ) • k) < β l by
        simpa using hlt))
      exact this.mono (fun e he => he.le)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hp := vi hx (hball (show dist (δ / 2) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith))
  have hn := vi hx (hball (show dist (-(δ / 2)) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith))
  simp only [add_sub_cancel_left, dot_smul_right] at hp hn
  have h1 : 0 ≤ dot x k := by nlinarith
  have h2 : dot x k ≤ 0 := by nlinarith
  linarith

theorem dot_add_left (u v w : ι → ℝ) : dot (u + v) w = dot u w + dot v w := by
  rw [dot_comm, dot_add_right, dot_comm w, dot_comm w]

theorem dot_smul_left (u v : ι → ℝ) (c : ℝ) : dot (c • u) v = c * dot u v := by
  rw [dot_comm, dot_smul_right, dot_comm]

/-- the linear map `v ↦ (⟪a l, v⟫)_{l ∈ S}` -/
def TS (a : L → ι → ℝ) (S : Finset L) : (ι → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun v := fun l => dot (a l.1) v
  map_add' u v := by funext l; simp [dot_add_right]
  map_smul' c v := by funext l; simp [dot_smul_right]

/-- vectors orthogonal to the kernel of `TS` -/
def VS (a : L → ι → ℝ) (S : Finset L) : Submodule ℝ (ι → ℝ) where
  carrier := {v | ∀ k, (∀ l ∈ S, dot (a l) k = 0) → dot v k = 0}
  add_mem' := by
    intro u v hu hv k hk
    rw [dot_add_left, hu k hk, hv k hk, add_zero]
  zero_mem' := by
    intro k _; simp [dot]
  smul_mem' := by
    intro c v hv k hk
    rw [dot_smul_left, hv k hk, mul_zero]

theorem piece_bound (S : Finset L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ι → ℝ,
    (∀ k, (∀ l ∈ S, dot (a l) k = 0) → dot v k = 0) → ‖v‖ ≤ K * ∑ l ∈ S, |dot (a l) v| := by
  let f : VS a S →ₗ[ℝ] (S → ℝ) := (TS a S).comp (VS a S).subtype
  have hinj : Function.Injective f := by
    intro u w huw
    have hd : ∀ l ∈ S, dot (a l) ((u : ι → ℝ) - w) = 0 := by
      intro l hl
      have := congrFun huw ⟨l, hl⟩
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, TS, LinearMap.coe_mk,
        AddHom.coe_mk] at this
      rw [dot_sub_right, this, sub_self]
    have hmem : ((u : ι → ℝ) - w) ∈ VS a S := Submodule.sub_mem _ u.2 w.2
    have := hmem _ hd
    exact Subtype.ext (sub_eq_zero.1 (dot_self_eq_zero this))
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz f).1 hinj
  refine ⟨K, K.2, fun v hv => ?_⟩
  have h := hK.le_mul_dist (⟨v, hv⟩ : VS a S) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h
  have hn : ‖(⟨v, hv⟩ : VS a S)‖ = ‖v‖ := rfl
  rw [hn] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ K.2)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun l _ => abs_nonneg _))).2 (fun l => ?_)
  simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, TS, LinearMap.coe_mk,
    AddHom.coe_mk, Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun l => |dot (a l) v|) (fun l _ => abs_nonneg _) l.2

theorem dot_sub_left (u v w : ι → ℝ) : dot (u - v) w = dot u w - dot v w := by
  rw [dot_comm, dot_sub_right, dot_comm w, dot_comm w]

theorem isCompact_ball (R : ℝ) : IsCompact {x : ι → ℝ | dot x x ≤ R} := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_dot_self continuous_const)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt R, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have := sq_le_dot_self x i
  have h2 : dot x x ≤ R := hx
  rw [sq]; linarith

/-- **Lipschitz continuity of the min-norm point of a polyhedron in the right-hand side.** -/
theorem minNorm_lipschitz : ∃ K : ℝ, 0 ≤ K ∧ ∀ (β1 β2 : L → ℝ) (x1 x2 : ι → ℝ),
    IsMinNorm a β1 x1 → IsMinNorm a β2 x2 → ‖x1 - x2‖ ≤ K * ‖β1 - β2‖ := by
  classical
  choose Kf hKf0 hKf using fun S : Finset L => piece_bound (a := a) S
  set Ktot : ℝ := ∑ S : Finset L, Kf S * (Fintype.card L : ℝ) with hKtot
  have hKS : ∀ S, Kf S * (Fintype.card L : ℝ) ≤ Ktot := fun S =>
    Finset.single_le_sum (f := fun S => Kf S * (Fintype.card L : ℝ))
      (fun S _ => mul_nonneg (hKf0 S) (Nat.cast_nonneg _)) (Finset.mem_univ S)
  have hK0 : 0 ≤ Ktot := (mul_nonneg (hKf0 ∅) (Nat.cast_nonneg _)).trans (hKS ∅)
  refine ⟨Ktot, hK0, ?_⟩
  intro β1 β2 x1 x2 h1 h2
  set Δ := β2 - β1 with hΔ
  let β : ℝ → L → ℝ := fun s => β1 + s • Δ
  have hβcomb : ∀ s, (1 - s) • β1 + s • β2 = β s := by
    intro s; funext l; simp only [β, hΔ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hβcomb2 : ∀ t e θ : ℝ, (1 - θ) • β t + θ • β e = β ((1 - θ) * t + θ * e) := by
    intro t e θ; funext l
    simp only [β, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hex : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ x, IsMinNorm a (β s) x := by
    intro s hs
    have := feas_comb h1.1 h2.1 s hs.1 hs.2
    rw [hβcomb] at this
    exact minNorm_exists this
  let f : ℝ → ι → ℝ := fun s => if h : ∃ x, IsMinNorm a (β s) x then Classical.choose h else 0
  have hf : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsMinNorm a (β s) (f s) := by
    intro s hs
    simp only [f, dif_pos (hex s hs)]
    exact Classical.choose_spec (hex s hs)
  have hf0 : f 0 = x1 := by
    have h := hf 0 ⟨le_refl _, zero_le_one⟩
    have e : β 0 = β1 := by funext l; simp [β]
    rw [e] at h
    exact minNorm_unique h h1
  have hf1 : f 1 = x2 := by
    have h := hf 1 ⟨zero_le_one, le_refl _⟩
    have e : β 1 = β2 := by funext l; simp [β, hΔ]
    rw [e] at h
    exact minNorm_unique h h2
  set R0 := max (dot x1 x1) (dot x2 x2) with hR0
  have hR0nn : 0 ≤ R0 := le_trans (dot_self_nonneg x1) (le_max_left _ _)
  have hbd : ∀ s ∈ Set.Icc (0 : ℝ) 1, dot (f s) (f s) ≤ R0 := by
    intro s hs
    have hfe := feas_comb h1.1 h2.1 s hs.1 hs.2
    rw [hβcomb] at hfe
    refine ((hf s hs).2 _ hfe).trans ((dot_comb_le x1 x2 s hs.1 hs.2).trans ?_)
    have := le_max_left (dot x1 x1) (dot x2 x2)
    have := le_max_right (dot x1 x1) (dot x2 x2)
    nlinarith [hs.1, hs.2]
  -- convex upper bound
  have hcomb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ e ∈ Set.Icc (0 : ℝ) 1, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      dot (f ((1 - θ) * t + θ * e)) (f ((1 - θ) * t + θ * e)) ≤ dot (f t) (f t) + θ * R0 := by
    intro t ht e he θ hθ0 hθ1
    have hs : (1 - θ) * t + θ * e ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [ht.1, he.1]
      · nlinarith [ht.2, he.2]
    have hfe := feas_comb (hf t ht).1 (hf e he).1 θ hθ0 hθ1
    rw [hβcomb2] at hfe
    refine ((hf _ hs).2 _ hfe).trans ((dot_comb_le _ _ θ hθ0 hθ1).trans ?_)
    have := hbd e he
    have := dot_self_nonneg (f t)
    nlinarith
  -- upper approximation
  have hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |s - t| < δ → dot (f s) (f s) ≤ dot (f t) (f t) + ε := by
    intro t ht ε hε
    set δ1 : ℝ := if t < 1 then ε * (1 - t) / (R0 + 1) else 1
    set δ2 : ℝ := if 0 < t then ε * t / (R0 + 1) else 1
    have hδ1 : 0 < δ1 := by
      simp only [δ1]; split_ifs with h
      · apply div_pos (mul_pos hε (by linarith)) (by linarith)
      · exact one_pos
    have hδ2 : 0 < δ2 := by
      simp only [δ2]; split_ifs with h
      · apply div_pos (mul_pos hε h) (by linarith)
      · exact one_pos
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs hst => ?_⟩
    rcases le_or_gt t s with hts | hts
    · by_cases ht1 : t < 1
      · set θ := (s - t) / (1 - t)
        have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
        have hθ1 : θ ≤ 1 := (div_le_one (by linarith)).2 (by linarith [hs.2])
        have hseq : (1 - θ) * t + θ * 1 = s := by
          have hne : (1 - t) ≠ 0 := by linarith
          simp only [θ]; field_simp; ring
        have := hcomb t ht 1 ⟨zero_le_one, le_refl _⟩ θ hθ0 hθ1
        rw [hseq] at this
        refine this.trans ?_
        have hlt : s - t < δ1 := by
          have := lt_of_lt_of_le hst (min_le_left _ _); rwa [abs_of_nonneg (by linarith)] at this
        have hδ1' : δ1 = ε * (1 - t) / (R0 + 1) := by simp [δ1, ht1]
        have : θ * R0 ≤ ε := by
          have h3 : θ < ε / (R0 + 1) := by
            rw [div_lt_div_iff₀ (by linarith) (by linarith)]
            rw [hδ1'] at hlt
            rw [lt_div_iff₀ (by linarith)] at hlt
            nlinarith
          have h4 : θ * R0 ≤ ε / (R0 + 1) * R0 := mul_le_mul_of_nonneg_right h3.le hR0nn
          have h5 : ε / (R0 + 1) * R0 ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
          linarith
        linarith
      · have : s = t := by linarith [hs.2, ht.2]
        rw [this]; linarith
    · have ht0 : 0 < t := lt_of_le_of_lt hs.1 hts
      set θ := (t - s) / t
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) ht0.le
      have hθ1 : θ ≤ 1 := (div_le_one ht0).2 (by linarith [hs.1])
      have hseq : (1 - θ) * t + θ * 0 = s := by
        simp only [θ]; field_simp; ring
      have := hcomb t ht 0 ⟨le_refl _, zero_le_one⟩ θ hθ0 hθ1
      rw [hseq] at this
      refine this.trans ?_
      have hlt : t - s < δ2 := by
        have := lt_of_lt_of_le hst (min_le_right _ _)
        rwa [abs_of_neg (by linarith), neg_sub] at this
      have hδ2' : δ2 = ε * t / (R0 + 1) := by simp [δ2, ht0]
      have : θ * R0 ≤ ε := by
        have h3 : θ < ε / (R0 + 1) := by
          rw [div_lt_div_iff₀ ht0 (by linarith)]
          rw [hδ2', lt_div_iff₀ (by linarith)] at hlt
          nlinarith
        have h4 : θ * R0 ≤ ε / (R0 + 1) * R0 := mul_le_mul_of_nonneg_right h3.le hR0nn
        have h5 : ε / (R0 + 1) * R0 ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
        linarith
      linarith
  -- continuity
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    intro t ht
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    by_contra hne
    push Not at hne
    have hseq : ∀ n : ℕ, ∃ s ∈ Set.Icc (0 : ℝ) 1, dist s t < 1 / ((n : ℝ) + 1) ∧
        ε ≤ dist (f s) (f t) := fun n => hne _ (by positivity)
    choose sq hsq hsqt hsqf using hseq
    obtain ⟨xs, -, φ, hφ, hlim⟩ := (isCompact_ball (ι := ι) R0).tendsto_subseq
      (x := fun n => f (sq n)) (fun n => hbd _ (hsq n))
    have hst : Tendsto (fun n => sq (φ n)) atTop (𝓝 t) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have : Tendsto sq atTop (𝓝 t) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun n => dist_nonneg) (fun n => (hsqt n).le) h0
      exact this.comp hφ.tendsto_atTop
    have hxs_feas : Feas a (β t) xs := by
      intro l
      have hl : ∀ n, dot (a l) (f (sq (φ n))) ≤ β (sq (φ n)) l :=
        fun n => (hf _ (hsq _)).1 l
      have hA : Tendsto (fun n => dot (a l) (f (sq (φ n)))) atTop (𝓝 (dot (a l) xs)) :=
        ((continuous_dot_left (a l)).tendsto xs).comp hlim
      have hB : Tendsto (fun n => β (sq (φ n)) l) atTop (𝓝 (β t l)) := by
        simp only [β, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact tendsto_const_nhds.add (hst.mul tendsto_const_nhds)
      exact le_of_tendsto_of_tendsto' hA hB hl
    have hxs_le : dot xs xs ≤ dot (f t) (f t) := by
      apply le_of_forall_pos_lt_add
      intro ε' hε'
      obtain ⟨δ, hδ, hδs⟩ := hupper t ht (ε' / 2) (by positivity)
      have hev : ∀ᶠ n in atTop, dot (f (sq (φ n))) (f (sq (φ n))) ≤ dot (f t) (f t) + ε' / 2 := by
        have := (Metric.tendsto_nhds.1 hst) δ hδ
        filter_upwards [this] with n hn
        exact hδs _ (hsq _) (by rw [← Real.dist_eq]; exact hn)
      have hC : Tendsto (fun n => dot (f (sq (φ n))) (f (sq (φ n)))) atTop (𝓝 (dot xs xs)) :=
        (continuous_dot_self.tendsto xs).comp hlim
      have := le_of_tendsto hC hev
      linarith
    have hxs_min : IsMinNorm a (β t) xs := ⟨hxs_feas, fun y hy => hxs_le.trans ((hf t ht).2 y hy)⟩
    have heq : xs = f t := minNorm_unique hxs_min (hf t ht)
    rw [heq] at hlim
    have := (Metric.tendsto_nhds.1 hlim) ε hε
    obtain ⟨n, hn⟩ := this.exists
    exact absurd (hsqf (φ n)) (not_le.2 hn)
  -- local step
  have hlocal : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Set.Icc 0 1] t,
      ‖f s - f t‖ ≤ Ktot * ‖Δ‖ * |s - t| := by
    intro t ht
    let Piece : Finset L → ℝ → Prop := fun S s =>
      (∀ k, (∀ l ∈ S, dot (a l) k = 0) → dot (f s) k = 0) ∧ ∀ l ∈ S, dot (a l) (f s) = β s l
    have hev : ∀ᶠ s in 𝓝[Set.Icc 0 1] t, ∀ S : Finset L, Piece S s → Piece S t := by
      rw [eventually_all]
      intro S
      by_cases hPt : Piece S t
      · exact Eventually.of_forall (fun _ _ => hPt)
      · simp only [Piece, not_and_or, not_forall] at hPt
        rcases hPt with ⟨k, hk, hne⟩ | ⟨l, hl, hne⟩
        · have hc : ContinuousWithinAt (fun s => dot (f s) k) (Set.Icc 0 1) t := by
            have : (fun s => dot (f s) k) = (fun s => dot k (f s)) := by
              funext s; exact dot_comm _ _
            rw [this]
            exact ((continuous_dot_left k).comp_continuousOn hcont) t ht
          filter_upwards [hc.tendsto.eventually_ne hne] with s hs hP
          exact absurd (hP.1 k hk) hs
        · have hc : ContinuousWithinAt (fun s => dot (a l) (f s) - β s l) (Set.Icc 0 1) t := by
            have h1 := ((continuous_dot_left (a l)).comp_continuousOn hcont) t ht
            have h2 : Continuous (fun s : ℝ => β s l) := by
              simp only [β, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop
            exact h1.sub h2.continuousWithinAt
          have hne' : dot (a l) (f t) - β t l ≠ 0 := sub_ne_zero.2 hne
          filter_upwards [hc.tendsto.eventually_ne hne', self_mem_nhdsWithin] with s hs _ hP
          exact absurd (sub_eq_zero.2 (hP.2 l hl)) hs
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hsI
    set S := Finset.univ.filter (fun l => dot (a l) (f s) = β s l)
    have hPs : Piece S s := by
      refine ⟨fun k hk => active_orth (hf s hsI) k (fun l hl => hk l (by simp [S, hl])),
        fun l hl => by simpa [S] using hl⟩
    have hPt := hs S hPs
    have hv : ∀ k, (∀ l ∈ S, dot (a l) k = 0) → dot (f s - f t) k = 0 := by
      intro k hk
      rw [dot_sub_left, hPs.1 k hk, hPt.1 k hk, sub_self]
    have hb := hKf S _ hv
    have hsum : ∑ l ∈ S, |dot (a l) (f s - f t)| ≤ (Fintype.card L : ℝ) * (‖Δ‖ * |s - t|) := by
      have : ∀ l ∈ S, |dot (a l) (f s - f t)| ≤ ‖Δ‖ * |s - t| := by
        intro l hl
        rw [dot_sub_right, hPs.2 l hl, hPt.2 l hl]
        simp only [β, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show β1 l + s * Δ l - (β1 l + t * Δ l) = (s - t) * Δ l by ring, abs_mul, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have := norm_le_pi_norm Δ l
        rwa [Real.norm_eq_abs] at this
      calc ∑ l ∈ S, |dot (a l) (f s - f t)| ≤ ∑ l ∈ S, ‖Δ‖ * |s - t| := Finset.sum_le_sum this
        _ = (S.card : ℝ) * (‖Δ‖ * |s - t|) := by simp
        _ ≤ (Fintype.card L : ℝ) * (‖Δ‖ * |s - t|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_univ S
    calc ‖f s - f t‖ ≤ Kf S * ∑ l ∈ S, |dot (a l) (f s - f t)| := hb
      _ ≤ Kf S * ((Fintype.card L : ℝ) * (‖Δ‖ * |s - t|)) :=
          mul_le_mul_of_nonneg_left hsum (hKf0 S)
      _ = (Kf S * (Fintype.card L : ℝ)) * (‖Δ‖ * |s - t|) := by ring
      _ ≤ Ktot * (‖Δ‖ * |s - t|) := mul_le_mul_of_nonneg_right (hKS S) (by positivity)
      _ = Ktot * ‖Δ‖ * |s - t| := by ring
  -- real induction
  let A : Set ℝ := {s | ‖f s - f 0‖ ≤ Ktot * ‖Δ‖ * s}
  have hAclosed : IsClosed (A ∩ Set.Icc 0 1) := by
    have hc : ContinuousOn (fun s => Ktot * ‖Δ‖ * s - ‖f s - f 0‖) (Set.Icc 0 1) := by
      apply ContinuousOn.sub (by fun_prop)
      exact (hcont.sub continuousOn_const).norm
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
    convert this using 1
    ext s; simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici,
      sub_nonneg]; tauto
  have h1A : (1 : ℝ) ∈ A := by
    apply hAclosed.mem_of_ge_of_forall_exists_gt (by simp [A]) zero_le_one
    rintro x ⟨hxA, hx0, hx1⟩
    have hev := hlocal x ⟨hx0, hx1.le⟩
    obtain ⟨δ, hδ, hδs'⟩ := Metric.mem_nhdsWithin_iff.1 hev
    have hδs : ∀ {y : ℝ}, dist y x < δ → y ∈ Set.Icc (0 : ℝ) 1 →
        ‖f y - f x‖ ≤ Ktot * ‖Δ‖ * |y - x| := fun hy hyI => hδs' ⟨hy, hyI⟩
    set s := min (x + δ / 2) 1
    have hxs : x < s := lt_min (by linarith) hx1
    have hs1 : s ≤ 1 := min_le_right _ _
    have hsd : dist s x < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have := min_le_left (x + δ / 2) 1; linarith
    have hb := hδs hsd ⟨by linarith, hs1⟩
    refine ⟨s, ?_, hxs, hs1⟩
    show ‖f s - f 0‖ ≤ Ktot * ‖Δ‖ * s
    have hxA' : ‖f x - f 0‖ ≤ Ktot * ‖Δ‖ * x := hxA
    rw [abs_of_pos (by linarith)] at hb
    calc ‖f s - f 0‖ = ‖(f s - f x) + (f x - f 0)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖f s - f x‖ + ‖f x - f 0‖ := norm_add_le _ _
      _ ≤ Ktot * ‖Δ‖ * (s - x) + Ktot * ‖Δ‖ * x := add_le_add hb hxA'
      _ = Ktot * ‖Δ‖ * s := by ring
  have : ‖f 1 - f 0‖ ≤ Ktot * ‖Δ‖ * 1 := h1A
  rw [hf0, hf1, mul_one, hΔ, norm_sub_rev x2 x1] at this
  rwa [norm_sub_rev β2 β1] at this

end FJPolyProj


open ForkJoinCtrl.Tracking

namespace FJL13

open FJPolyProj

variable (N : Network)

abbrev Idx : Type := Fin N.J ⊕ (Fin N.I × Fin N.J)

abbrev LIdx : Type :=
  Fin N.K ⊕ (Fin N.I × Fin N.J) ⊕ Fin N.I ⊕ Fin N.I ⊕ (Fin N.I × Fin N.J) ⊕ (Fin N.I × Fin N.J)

def enc (x : LPVar N) : Idx N → ℝ := Sum.elim x.y (fun p => x.q p.1 p.2)

def dec (v : Idx N → ℝ) : LPVar N := ⟨fun j => v (Sum.inl j), fun i j => v (Sum.inr (i, j))⟩

theorem dec_enc (x : LPVar N) : dec N (enc N x) = x := by
  cases x; rfl

theorem enc_dec (v : Idx N → ℝ) : enc N (dec N v) = v := by
  funext c; cases c <;> rfl

theorem enc_injective : Function.Injective (enc N) := by
  intro x x' h
  rw [← dec_enc N x, ← dec_enc N x', h]

noncomputable def eY (j : Fin N.J) : Idx N → ℝ := Pi.single (Sum.inl j) 1
noncomputable def eQ (i : Fin N.I) (j : Fin N.J) : Idx N → ℝ := Pi.single (Sum.inr (i, j)) 1

variable {N}

theorem dot_single {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι) (v : ι → ℝ) :
    dot (Pi.single c 1) v = v c := by
  simp [dot, Pi.single_apply]

theorem dot_eY (j : Fin N.J) (v : Idx N → ℝ) : dot (eY N j) v = v (Sum.inl j) := dot_single _ _
theorem dot_eQ (i : Fin N.I) (j : Fin N.J) (v : Idx N → ℝ) :
    dot (eQ N i j) v = v (Sum.inr (i, j)) := dot_single _ _

theorem dot_neg_left' {ι : Type*} [Fintype ι] (u v : ι → ℝ) : dot (-u) v = -dot u v := by
  simp [dot, Finset.sum_neg_distrib]

theorem dot_zero_left' {ι : Type*} [Fintype ι] (v : ι → ℝ) : dot 0 v = 0 := by simp [dot]

theorem dot_sum_left' {ι κ : Type*} [Fintype ι] (s : Finset κ) (u : κ → ι → ℝ) (v : ι → ℝ) :
    dot (∑ k ∈ s, u k) v = ∑ k ∈ s, dot (u k) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, dot_add_left, ih]

variable (N)

/-- the LP constraint vectors (18b)-(18e) and the pinning of non-incident `q` -/
noncomputable def aLP : LIdx N → Idx N → ℝ
  | .inl k => -eY N (N.own k)
  | .inr (.inl p) => if N.P p.1 p.2 = true then eQ N p.1 p.2 - eY N p.2 else 0
  | .inr (.inr (.inl i)) => ∑ j ∈ N.Ji i, (1 / N.mu i j) • eQ N i j
  | .inr (.inr (.inr (.inl i))) => -∑ j ∈ N.Ji i, (1 / N.mu i j) • eQ N i j
  | .inr (.inr (.inr (.inr (.inl p)))) => -eQ N p.1 p.2
  | .inr (.inr (.inr (.inr (.inr p)))) => if N.P p.1 p.2 = true then 0 else eQ N p.1 p.2

noncomputable def bLP (b : LPParam N) : LIdx N → ℝ
  | .inl k => -b.1 k
  | .inr (.inl _) => 0
  | .inr (.inr (.inl i)) => b.2 i
  | .inr (.inr (.inr (.inl i))) => -b.2 i
  | .inr (.inr (.inr (.inr (.inl _)))) => 0
  | .inr (.inr (.inr (.inr (.inr _)))) => 0

/-- all QP constraints: the LP ones and (19e) -/
noncomputable def aQP : LIdx N ⊕ Unit → Idx N → ℝ
  | .inl l => aLP N l
  | .inr _ => ∑ j, N.h j • eY N j

noncomputable def bQP (b : LPParam N) : LIdx N ⊕ Unit → ℝ
  | .inl l => bLP N b l
  | .inr _ => z N b

variable {N}

theorem dot_wsum (i : Fin N.I) (v : Idx N → ℝ) :
    dot (∑ j ∈ N.Ji i, (1 / N.mu i j) • eQ N i j) v = ∑ j ∈ N.Ji i, v (Sum.inr (i, j)) / N.mu i j := by
  rw [dot_sum_left']
  apply Finset.sum_congr rfl; intro j _
  rw [dot_smul_left, dot_eQ]; ring

theorem feasLP_iff (b : LPParam N) (v : Idx N → ℝ) :
    Feas (aLP N) (bLP N b) v ↔ LPFeasible N b (dec N v) := by
  simp only [Feas, Sum.forall, aLP, bLP, LPFeasible, dec]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun k => ?_, fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
    · have := h1 k; rw [dot_neg_left', dot_eY] at this; linarith
    · have := h2 (i, j); simp only [hij, if_true, dot_sub_left, dot_eQ, dot_eY] at this; linarith
    · have := h3 i; have := h4 i; rw [dot_neg_left', dot_wsum] at *; linarith
    · have := h5 (i, j); rw [dot_neg_left', dot_eQ] at this; linarith
    · have := h6 (i, j); have := h5 (i, j)
      simp only [hij, Bool.false_eq_true, if_false, dot_eQ, dot_neg_left'] at *; linarith
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun k => ?_, fun p => ?_, fun i => ?_, fun i => ?_, fun p => ?_, fun p => ?_⟩
    · rw [dot_neg_left', dot_eY]; linarith [h1 k]
    · split_ifs with hp
      · rw [dot_sub_left, dot_eQ, dot_eY]; linarith [h2 p.1 p.2 hp]
      · rw [dot_zero_left']
    · rw [dot_wsum, h3 i]
    · rw [dot_neg_left', dot_wsum, h3 i]
    · rw [dot_neg_left', dot_eQ]
      by_cases hp : N.P p.1 p.2 = true
      · linarith [h4 p.1 p.2 hp]
      · rw [h5 p.1 p.2 (by simpa using hp)]; simp
    · split_ifs with hp
      · rw [dot_zero_left']
      · rw [dot_eQ, h5 p.1 p.2 (by simpa using hp)]

theorem dot_hvec (v : Idx N → ℝ) : dot (∑ j, N.h j • eY N j) v = LPObj N (dec N v) := by
  rw [dot_sum_left']
  simp only [LPObj, dec]
  apply Finset.sum_congr rfl; intro j _
  rw [dot_smul_left, dot_eY]

theorem feasQP_iff (b : LPParam N) (v : Idx N → ℝ) :
    Feas (aQP N) (bQP N b) v ↔ QPFeasible N b (dec N v) := by
  constructor
  · intro h
    refine ⟨(feasLP_iff b v).1 (fun l => h (Sum.inl l)), ?_⟩
    have := h (Sum.inr ())
    simp only [aQP, bQP, dot_hvec] at this
    exact this
  · rintro ⟨h1, h2⟩ l
    cases l with
    | inl l => exact (feasLP_iff b v).2 h1 l
    | inr u =>
      show dot (∑ j, N.h j • eY N j) v ≤ z N b
      rw [dot_hvec]; exact h2

theorem dot_self_eq_QPObj (b : LPParam N) (v : Idx N → ℝ) (hv : LPFeasible N b (dec N v)) :
    dot v v = QPObj N (dec N v) := by
  simp only [dot, QPObj, dec, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl; intro j _; ring
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => N.P i j = true)]
    have h0 : ∑ i ∈ Finset.univ.filter (fun i => ¬ N.P i j = true),
        v (Sum.inr (i, j)) * v (Sum.inr (i, j)) = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      have hp : N.P i j = false := by simpa using (Finset.mem_filter.1 hi).2
      have : v (Sum.inr (i, j)) = 0 := hv.2.2.2.2 i j hp
      rw [this]; ring
    rw [h0, add_zero]
    simp only [Network.Ij]
    apply Finset.sum_congr rfl; intro i _; ring

theorem qpopt_iff (b : LPParam N) (x : LPVar N) :
    QPOpt N b x ↔ IsMinNorm (aQP N) (bQP N b) (enc N x) := by
  constructor
  · rintro ⟨hf, hmin⟩
    have hf' : Feas (aQP N) (bQP N b) (enc N x) := by rw [feasQP_iff, dec_enc]; exact hf
    refine ⟨hf', fun v hv => ?_⟩
    have hv' := (feasQP_iff b v).1 hv
    rw [dot_self_eq_QPObj b (enc N x) (by rw [dec_enc]; exact hf.1), dec_enc,
      dot_self_eq_QPObj b v hv'.1]
    exact hmin _ hv'
  · rintro ⟨hf, hmin⟩
    have hf' := (feasQP_iff b _).1 hf
    rw [dec_enc] at hf'
    refine ⟨hf', fun x' hx' => ?_⟩
    have h1 : Feas (aQP N) (bQP N b) (enc N x') := by rw [feasQP_iff, dec_enc]; exact hx'
    have := hmin _ h1
    rw [dot_self_eq_QPObj b (enc N x) (by rw [dec_enc]; exact hf'.1),
      dot_self_eq_QPObj b (enc N x') (by rw [dec_enc]; exact hx'.1), dec_enc, dec_enc] at this
    exact this

theorem coord1_le (b1 b2 : LPParam N) (k : Fin N.K) : |b1.1 k - b2.1 k| ≤ ‖b1 - b2‖ := by
  have h1 : ‖(b1 - b2).1 k‖ ≤ ‖(b1 - b2).1‖ := norm_le_pi_norm _ k
  have h2 : ‖(b1 - b2).1‖ ≤ ‖b1 - b2‖ := norm_fst_le _
  have : ‖(b1 - b2).1 k‖ = |b1.1 k - b2.1 k| := by simp [Real.norm_eq_abs]
  linarith

theorem coord2_le (b1 b2 : LPParam N) (i : Fin N.I) : |b1.2 i - b2.2 i| ≤ ‖b1 - b2‖ := by
  have h1 : ‖(b1 - b2).2 i‖ ≤ ‖(b1 - b2).2‖ := norm_le_pi_norm _ i
  have h2 : ‖(b1 - b2).2‖ ≤ ‖b1 - b2‖ := norm_snd_le _
  have : ‖(b1 - b2).2 i‖ = |b1.2 i - b2.2 i| := by simp [Real.norm_eq_abs]
  linarith

theorem feas_nonempty (b : LPParam N) (hb : b.Nonneg) : ∃ x, LPFeasible N b x := by
  classical
  let q : Fin N.I → Fin N.J → ℝ := fun i j =>
    if N.P i j = true then N.mu i j * b.2 i / ((N.Ji i).card : ℝ) else 0
  refine ⟨⟨fun j => ∑ k, b.1 k + ∑ i, q i j, q⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have hq : ∀ i, 0 ≤ q i (N.own k) := by
      intro i; simp only [q]; split_ifs with h
      · exact div_nonneg (mul_nonneg (N.mu_pos _ _ h).le (hb.2 i)) (Nat.cast_nonneg _)
      · exact le_refl _
    have h1 : b.1 k ≤ ∑ k, b.1 k :=
      Finset.single_le_sum (fun k _ => hb.1 k) (Finset.mem_univ k)
    have h2 : 0 ≤ ∑ i, q i (N.own k) := Finset.sum_nonneg (fun i _ => hq i)
    show b.1 k ≤ ∑ k, b.1 k + ∑ i, q i (N.own k)
    linarith
  · intro i j hij
    have hq : ∀ i, 0 ≤ q i j := by
      intro i; simp only [q]; split_ifs with h
      · exact div_nonneg (mul_nonneg (N.mu_pos _ _ h).le (hb.2 i)) (Nat.cast_nonneg _)
      · exact le_refl _
    have h1 : q i j ≤ ∑ i, q i j := Finset.single_le_sum (fun i _ => hq i) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ k, b.1 k := Finset.sum_nonneg (fun k _ => hb.1 k)
    show 0 ≤ ∑ k, b.1 k + ∑ i, q i j - q i j
    linarith
  · intro i
    have hc : (0 : ℝ) < ((N.Ji i).card : ℝ) := by
      have : 2 ≤ (N.Ji i).card := N.two_le_card_types i
      exact_mod_cast (by omega : 0 < (N.Ji i).card)
    have : ∀ j ∈ N.Ji i, q i j / N.mu i j = b.2 i / ((N.Ji i).card : ℝ) := by
      intro j hj
      have hij : N.P i j = true := by simpa [Network.Ji] using hj
      have hmu := N.mu_pos i j hij
      simp only [q, hij, if_true]
      field_simp
    show ∑ j ∈ N.Ji i, q i j / N.mu i j = b.2 i
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    field_simp
  · intro i j hij
    show 0 ≤ q i j
    simp only [q, hij, if_true]
    exact div_nonneg (mul_nonneg (N.mu_pos _ _ hij).le (hb.2 i)) (Nat.cast_nonneg _)
  · intro i j hij
    show q i j = 0
    simp [q, hij]

/-- trimming `y` to the inner maxima keeps feasibility and does not increase the objective -/
theorem trim (b : LPParam N) (x : LPVar N) (hx : LPFeasible N b x) :
    LPFeasible N b ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩ ∧
    LPObj N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩ ≤ LPObj N x := by
  refine ⟨⟨?_, ?_, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩, ?_⟩
  · intro k
    unfold Network.jobMax
    apply Finset.le_max'
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨k, by simp [Network.Kj], rfl⟩
  · intro i j hij
    simp only [sub_nonneg]
    unfold Network.jobMax
    apply Finset.le_max'
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨i, by simp [Network.Ij, hij], rfl⟩
  · have hjm : ∀ j, N.jobMax j b.1 (fun i => x.q i j) ≤ x.y j := by
      intro j
      unfold Network.jobMax
      apply Finset.max'_le
      intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
        have : N.own k = j := by simpa [Network.Kj] using hk
        rw [← this]; exact hx.1 k
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
        have : N.P i j = true := by simpa [Network.Ij] using hi
        have := hx.2.1 i j this
        linarith
    unfold LPObj
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hjm j) (N.h_nonneg j)

/-- the LP (18) attains its infimum -/
theorem lp_attain (b : LPParam N) (hb : b.Nonneg) :
    ∃ x, LPFeasible N b x ∧ LPObj N x = z N b := by
  classical
  set B : ℝ := ∑ k, |b.1 k| + ∑ i, ∑ j, |N.mu i j| * |b.2 i| with hB
  have hB0 : 0 ≤ B := add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _)
      (abs_nonneg _))))
  -- coordinate bounds for a trimmed feasible point
  have hqB : ∀ x : LPVar N, LPFeasible N b x → ∀ i j, 0 ≤ x.q i j ∧ x.q i j ≤ B := by
    intro x hx i j
    by_cases hij : N.P i j = true
    · have h0 := hx.2.2.2.1 i j hij
      refine ⟨h0, ?_⟩
      have hmu := N.mu_pos i j hij
      have hj : j ∈ N.Ji i := by simp [Network.Ji, hij]
      have hle : x.q i j / N.mu i j ≤ b.2 i := by
        rw [← hx.2.2.1 i]
        exact Finset.single_le_sum (f := fun j => x.q i j / N.mu i j)
          (fun j' hj' => div_nonneg (hx.2.2.2.1 i j' (by simpa [Network.Ji] using hj'))
            (N.mu_pos i j' (by simpa [Network.Ji] using hj')).le) hj
      have h1 : x.q i j ≤ |N.mu i j| * |b.2 i| := by
        rw [div_le_iff₀ hmu] at hle
        rw [abs_of_pos hmu]
        nlinarith [le_abs_self (b.2 i)]
      have h2 : |N.mu i j| * |b.2 i| ≤ ∑ j, |N.mu i j| * |b.2 i| :=
        Finset.single_le_sum (f := fun j => |N.mu i j| * |b.2 i|)
          (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
      have h3 : ∑ j, |N.mu i j| * |b.2 i| ≤ ∑ i, ∑ j, |N.mu i j| * |b.2 i| :=
        Finset.single_le_sum (f := fun i => ∑ j, |N.mu i j| * |b.2 i|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
          (Finset.mem_univ i)
      have h4 : 0 ≤ ∑ k, |b.1 k| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith
    · rw [hx.2.2.2.2 i j (by simpa using hij)]; exact ⟨le_refl _, hB0⟩
  have hkB : ∀ k, b.1 k ≤ B := by
    intro k
    have h1 : b.1 k ≤ |b.1 k| := le_abs_self _
    have h2 : |b.1 k| ≤ ∑ k, |b.1 k| := Finset.single_le_sum (f := fun k => |b.1 k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 : 0 ≤ ∑ i, ∑ j, |N.mu i j| * |b.2 i| :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _)
        (abs_nonneg _)))
    linarith
  set M : ℝ := (Fintype.card (Idx N) : ℝ) * B ^ 2
  have htrim_bd : ∀ x : LPVar N, LPFeasible N b x →
      dot (enc N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩)
        (enc N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩) ≤ M := by
    intro x hx
    have hc : ∀ c, |enc N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩ c| ≤ B := by
      intro c
      cases c with
      | inl j =>
        simp only [enc, Sum.elim_inl]
        obtain ⟨i, hi⟩ := N.exists_server j
        have hlow : x.q i j ≤ N.jobMax j b.1 (fun i => x.q i j) := by
          unfold Network.jobMax
          apply Finset.le_max'
          apply Finset.mem_union_right
          exact Finset.mem_image.2 ⟨i, by simp [Network.Ij, hi], rfl⟩
        have hup : N.jobMax j b.1 (fun i => x.q i j) ≤ B := by
          unfold Network.jobMax
          apply Finset.max'_le
          intro c hc
          rcases Finset.mem_union.1 hc with hc | hc
          · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hc; exact hkB k
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc; exact (hqB x hx i j).2
        rw [abs_le]; constructor <;> linarith [(hqB x hx i j).1]
      | inr p =>
        simp only [enc, Sum.elim_inr]
        rw [abs_le]; constructor <;> linarith [(hqB x hx p.1 p.2).1, (hqB x hx p.1 p.2).2]
    simp only [dot, M]
    calc ∑ c, enc N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩ c *
          enc N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩ c ≤ ∑ c : Idx N, B ^ 2 := by
          apply Finset.sum_le_sum; intro c _
          have := hc c
          have : |enc N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩ c| ^ 2 ≤ B ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) this 2
          rw [sq_abs] at this; nlinarith
      _ = (Fintype.card (Idx N) : ℝ) * B ^ 2 := by simp
  -- compact search set
  set Kc := {v | Feas (aLP N) (bLP N b) v} ∩ {v : Idx N → ℝ | dot v v ≤ M}
  have hKc : IsCompact Kc := (isCompact_ball M).inter_left (isClosed_feas _)
  obtain ⟨x0, hx0⟩ := feas_nonempty b hb
  have hx0t := trim b x0 hx0
  have hmem0 : enc N ⟨fun j => N.jobMax j b.1 (fun i => x0.q i j), x0.q⟩ ∈ Kc := by
    refine ⟨?_, htrim_bd x0 hx0⟩
    show Feas (aLP N) (bLP N b) _
    rw [feasLP_iff, dec_enc]; exact hx0t.1
  have hne : Kc.Nonempty := ⟨_, hmem0⟩
  obtain ⟨v, hvK, hvmin⟩ := hKc.exists_isMinOn hne
    (continuous_dot_left (∑ j, N.h j • eY N j)).continuousOn
  have hvf : LPFeasible N b (dec N v) := (feasLP_iff b v).1 hvK.1
  have hleast : IsLeast (LPObj N '' {x | LPFeasible N b x}) (LPObj N (dec N v)) := by
    refine ⟨⟨_, hvf, rfl⟩, ?_⟩
    rintro c ⟨x, hx, rfl⟩
    have ht := trim b x hx
    have hmem : enc N ⟨fun j => N.jobMax j b.1 (fun i => x.q i j), x.q⟩ ∈ Kc := by
      refine ⟨?_, htrim_bd x hx⟩
      show Feas (aLP N) (bLP N b) _
      rw [feasLP_iff, dec_enc]; exact ht.1
    have := hvmin hmem
    simp only [Set.mem_setOf_eq, dot_hvec, dec_enc] at this
    exact this.trans ht.2
  exact ⟨dec N v, hvf, (hleast.csInf_eq).symm⟩

theorem bQP_lip (C1 : ℝ) (hC1 : 0 < C1)
    (hz : ∀ b1 b2 : LPParam N, b1.Nonneg → b2.Nonneg → |z N b1 - z N b2| ≤ C1 * ‖b1 - b2‖)
    (b1 b2 : LPParam N) (hb1 : b1.Nonneg) (hb2 : b2.Nonneg) :
    ‖bQP N b1 - bQP N b2‖ ≤ (1 + C1) * ‖b1 - b2‖ := by
  have hn := norm_nonneg (b1 - b2)
  have hd : ‖b1 - b2‖ ≤ (1 + C1) * ‖b1 - b2‖ := by nlinarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun l => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  rcases l with u | k
  · rcases u with k | p | i | i | p | p <;>
      simp only [bQP, bLP, sub_self, abs_zero]
    · rw [show -b1.1 k - -b2.1 k = -(b1.1 k - b2.1 k) by ring, abs_neg]
      exact (coord1_le b1 b2 k).trans hd
    · positivity
    · exact (coord2_le b1 b2 i).trans hd
    · rw [show -b1.2 i - -b2.2 i = -(b1.2 i - b2.2 i) by ring, abs_neg]
      exact (coord2_le b1 b2 i).trans hd
    · positivity
    · positivity
  · simp only [bQP]
    refine (hz b1 b2 hb1 hb2).trans ?_
    nlinarith

end FJL13

theorem solution (N : Network) :
    (∀ b : LPParam N, b.Nonneg → ∃! x : LPVar N, QPOpt N b x) ∧
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ (b1 b2 : LPParam N) (x1 x2 : LPVar N), b1.Nonneg → b2.Nonneg →
      QPOpt N b1 x1 → QPOpt N b2 x2 → ∀ i j, N.P i j = true →
        |x1.q i j - x2.q i j| ≤ C2 * ‖b1 - b2‖ := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨x, hx, hxz⟩ := FJL13.lp_attain b hb
    have hfe : FJPolyProj.Feas (FJL13.aQP N) (FJL13.bQP N b) (FJL13.enc N x) := by
      rw [FJL13.feasQP_iff, FJL13.dec_enc]; exact ⟨hx, hxz.le⟩
    obtain ⟨v, hv⟩ := FJPolyProj.minNorm_exists hfe
    refine ⟨FJL13.dec N v, ?_, ?_⟩
    · show QPOpt N b (FJL13.dec N v)
      rw [FJL13.qpopt_iff, FJL13.enc_dec]; exact hv
    · intro x' hx'
      rw [FJL13.qpopt_iff] at hx'
      apply FJL13.enc_injective N
      rw [FJL13.enc_dec]
      exact FJPolyProj.minNorm_unique hx' hv
  · obtain ⟨K, hK0, hK⟩ := FJPolyProj.minNorm_lipschitz (a := FJL13.aQP N)
    obtain ⟨_, C1, hC1, hz⟩ := ForkJoinCtrl.Tracking.lemma_1_part_2 N
    refine ⟨K * (1 + C1) + 1, by positivity, ?_⟩
    intro b1 b2 x1 x2 hb1 hb2 h1 h2 i j _
    rw [FJL13.qpopt_iff] at h1 h2
    have hx := hK _ _ _ _ h1 h2
    have hb := FJL13.bQP_lip C1 hC1 hz b1 b2 hb1 hb2
    have hc : |x1.q i j - x2.q i j| ≤ ‖FJL13.enc N x1 - FJL13.enc N x2‖ := by
      have := norm_le_pi_norm (FJL13.enc N x1 - FJL13.enc N x2) (Sum.inr (i, j))
      simpa [FJL13.enc, Real.norm_eq_abs] using this
    have hn := norm_nonneg (b1 - b2)
    calc |x1.q i j - x2.q i j| ≤ K * ‖FJL13.bQP N b1 - FJL13.bQP N b2‖ := hc.trans hx
      _ ≤ K * ((1 + C1) * ‖b1 - b2‖) := mul_le_mul_of_nonneg_left hb hK0
      _ ≤ (K * (1 + C1) + 1) * ‖b1 - b2‖ := by nlinarith
