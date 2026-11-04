-- Prove2me | solution 1 for ConvexSDDP.Stoch.lemma_3_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:13:00.180557+00:00
-- url     : https://prove2.me/submissions/68063f12-0bbd-4206-9174-106442554e37

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_i
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_ii
import Theorems.Thm_ConvexSDDP_Stoch_eq_26
open StochasticProg.Multistage Filter Topology
open scoped Pointwise

namespace SolL31iii
open ConvexSDDP.Det

lemma econvex_iff {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (g : Z → EReal) :
    EConvex g ↔ ∀ x y : Z, ∀ r s : ℝ, g x ≤ r → g y ≤ s → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g ((1 - t) • x + t • y) ≤ (((1 - t) * r + t * s : ℝ) : EReal) := by
  constructor
  · intro h x y r s hx hy t ht0 ht1
    have := h (x := (x, r)) hx (y := (y, s)) hy (a := 1 - t) (b := t) (by linarith) ht0
      (by ring)
    simpa using this
  · intro h p hp q hq a b ha hb hab
    have ha' : a = 1 - b := by linarith
    subst ha'
    have := h p.1 q.1 p.2 q.2 hp hq b hb (by linarith)
    simpa using this

lemma ereal_le_of_forall_pos (a : EReal) (c : ℝ) (h : ∀ ε : ℝ, 0 < ε → a ≤ ((c + ε : ℝ) : EReal)) :
    a ≤ (c : EReal) := by
  refine le_of_forall_gt_imp_ge_of_dense (fun b hb => ?_)
  obtain ⟨x, hcx, hxb⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  have hcx' : c < x := by exact_mod_cast hcx
  have := h (x - c) (by linarith)
  rw [show c + (x - c) = x by ring] at this
  exact this.trans hxb.le

lemma econvex_const_zero {Z : Type*} [AddCommGroup Z] [Module ℝ Z] :
    EConvex (fun _ : Z => (0 : EReal)) := by
  rw [econvex_iff]
  intro x y r s hx hy t ht0 ht1
  have hr : (0 : ℝ) ≤ r := by exact_mod_cast hx
  have hs : (0 : ℝ) ≤ s := by exact_mod_cast hy
  have : (0 : ℝ) ≤ (1 - t) * r + t * s := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) hr
    have := mul_nonneg ht0 hs
    linarith
  exact_mod_cast this

lemma econvex_add {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (g h : Z → EReal)
    (hgb : ∀ z, g z ≠ ⊥) (hhb : ∀ z, h z ≠ ⊥) (hg : EConvex g) (hh : EConvex h) :
    EConvex (fun z => g z + h z) := by
  rw [econvex_iff] at hg hh ⊢
  intro x y r s hx hy t ht0 ht1
  have fin : ∀ z (r : ℝ), g z + h z ≤ r → g z ≠ ⊤ ∧ h z ≠ ⊤ := by
    intro z r hz
    constructor
    · intro htop
      rw [htop, EReal.top_add_of_ne_bot (hhb z)] at hz
      exact absurd hz (not_le.2 (EReal.coe_lt_top r))
    · intro htop
      rw [htop, EReal.add_top_of_ne_bot (hgb z)] at hz
      exact absurd hz (not_le.2 (EReal.coe_lt_top r))
  obtain ⟨hgx, hhx⟩ := fin x r hx
  obtain ⟨hgy, hhy⟩ := fin y s hy
  have ex := EReal.coe_toReal hgx (hgb x)
  have ex' := EReal.coe_toReal hhx (hhb x)
  have ey := EReal.coe_toReal hgy (hgb y)
  have ey' := EReal.coe_toReal hhy (hhb y)
  have hx' : (g x).toReal + (h x).toReal ≤ r := by
    rw [← ex, ← ex', ← EReal.coe_add] at hx; exact_mod_cast hx
  have hy' : (g y).toReal + (h y).toReal ≤ s := by
    rw [← ey, ← ey', ← EReal.coe_add] at hy; exact_mod_cast hy
  have h1 := hg x y (g x).toReal (g y).toReal ex.ge ey.ge t ht0 ht1
  have h2 := hh x y (r - (g x).toReal) (s - (g y).toReal)
    (by rw [← ex']; exact_mod_cast (by linarith)) (by rw [← ey']; exact_mod_cast (by linarith))
    t ht0 ht1
  refine (add_le_add h1 h2).trans ?_
  rw [← EReal.coe_add]
  exact_mod_cast (by nlinarith)

lemma econvex_smul {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (c : ℝ) (hc : 0 ≤ c)
    (g : Z → EReal) (hgb : ∀ z, g z ≠ ⊥) (hg : EConvex g) :
    EConvex (fun z => (c : EReal) * g z) := by
  rcases hc.eq_or_lt with h0 | hpos
  · subst h0
    simpa using (econvex_const_zero (Z := Z))
  rw [econvex_iff] at hg ⊢
  intro x y r s hx hy t ht0 ht1
  have fin : ∀ z (r : ℝ), (c : EReal) * g z ≤ r → g z ≠ ⊤ := by
    intro z r hz htop
    rw [htop, EReal.coe_mul_top_of_pos hpos] at hz
    exact absurd hz (not_le.2 (EReal.coe_lt_top r))
  have ex := EReal.coe_toReal (fin x r hx) (hgb x)
  have ey := EReal.coe_toReal (fin y s hy) (hgb y)
  have hx' : (g x).toReal ≤ r / c := by
    rw [← ex, ← EReal.coe_mul] at hx
    rw [le_div_iff₀ hpos]; have := (EReal.coe_le_coe_iff.1 hx); linarith
  have hy' : (g y).toReal ≤ s / c := by
    rw [← ey, ← EReal.coe_mul] at hy
    rw [le_div_iff₀ hpos]; have := (EReal.coe_le_coe_iff.1 hy); linarith
  have h1 := hg x y (r / c) (s / c) (by rw [← ex]; exact_mod_cast hx')
    (by rw [← ey]; exact_mod_cast hy') t ht0 ht1
  refine (mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.2 hc)).trans (le_of_eq ?_)
  rw [← EReal.coe_mul]
  congr 1
  field_simp

lemma econvex_sum {Z ι : Type*} [AddCommGroup Z] [Module ℝ Z] (s : Finset ι)
    (g : ι → Z → EReal) (hgb : ∀ i ∈ s, ∀ z, g i z ≠ ⊥) (hg : ∀ i ∈ s, EConvex (g i)) :
    EConvex (fun z => ∑ i ∈ s, g i z) ∧ ∀ z, ∑ i ∈ s, g i z ≠ ⊥ := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨econvex_const_zero, fun _ => by simp⟩
  | cons a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hgb i (Finset.mem_cons_of_mem hi))
      (fun i hi => hg i (Finset.mem_cons_of_mem hi))
    simp only [Finset.sum_cons]
    refine ⟨econvex_add _ _ (hgb a (Finset.mem_cons_self a s)) ih2
      (hg a (Finset.mem_cons_self a s)) ih1, fun z => ?_⟩
    exact EReal.add_ne_bot_iff.2 ⟨hgb a (Finset.mem_cons_self a s) z, ih2 z⟩

open Classical in
lemma econvex_restrict {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (X : Set Z) (hX : Convex ℝ X)
    (g : Z → EReal) (hg : EConvex g) :
    EConvex (fun z => if z ∈ X then g z else ⊤) := by
  classical
  rw [econvex_iff] at hg ⊢
  intro x y r s hx hy t ht0 ht1
  by_cases hxX : x ∈ X
  · by_cases hyX : y ∈ X
    · rw [if_pos hxX] at hx
      rw [if_pos hyX] at hy
      have hz : (1 - t) • x + t • y ∈ X := hX hxX hyX (by linarith) ht0 (by ring)
      rw [if_pos hz]
      exact hg x y r s hx hy t ht0 ht1
    · rw [if_neg hyX] at hy
      exact absurd hy (not_le.2 (EReal.coe_lt_top s))
  · rw [if_neg hxX] at hx
    exact absurd hx (not_le.2 (EReal.coe_lt_top r))

lemma econvex_comp_linear {Z Z' : Type*} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup Z']
    [Module ℝ Z'] (g : Z' → EReal) (hg : EConvex g) (A : Z →ₗ[ℝ] Z') :
    EConvex (fun z => g (A z)) := by
  rw [econvex_iff] at hg ⊢
  intro x y r s hx hy t ht0 ht1
  simp only [map_add, map_smul]
  exact hg _ _ r s hx hy t ht0 ht1

lemma econvex_pinf {Z W : Type*} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup W] [Module ℝ W]
    (U : Z → Set W) (hU : ConvexMultifunction U) (φ : Z × W → EReal) (hφ : EConvex φ) :
    EConvex (fun z => ⨅ u ∈ U z, φ (z, u)) := by
  rw [econvex_iff] at hφ ⊢
  intro x y r s hx hy t ht0 ht1
  rcases ht0.eq_or_lt with h0 | ht0'
  · subst h0
    simpa using hx
  rcases ht1.eq_or_lt with h1 | ht1'
  · subst h1
    simpa using hy
  apply ereal_le_of_forall_pos
  intro ε hε
  have hx2 : ⨅ u ∈ U x, φ (x, u) < ((r + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hx (by exact_mod_cast (by linarith : r < r + ε))
  have hy2 : ⨅ u ∈ U y, φ (y, u) < ((s + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hy (by exact_mod_cast (by linarith : s < s + ε))
  obtain ⟨u1, hu1⟩ := iInf_lt_iff.1 hx2
  obtain ⟨hu1U, hu1'⟩ := iInf_lt_iff.1 hu1
  obtain ⟨u2, hu2⟩ := iInf_lt_iff.1 hy2
  obtain ⟨hu2U, hu2'⟩ := iInf_lt_iff.1 hu2
  have hmem := hU x y u1 hu1U u2 hu2U t ht0' ht1'
  have hc := hφ (x, u1) (y, u2) (r + ε) (s + ε) hu1'.le hu2'.le t ht0 ht1
  refine (biInf_le (fun u => φ ((1 - t) • x + t • y, u)) hmem).trans ?_
  have e : (1 - t) • (x, u1) + t • (y, u2) = ((1 - t) • x + t • y, (1 - t) • u1 + t • u2) := by
    ext <;> simp
  rw [e] at hc
  refine hc.trans (le_of_eq ?_)
  congr 1
  ring


lemma lipschitz_of_convexOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) (f : E → ℝ)
    (hf : ConvexOn ℝ (K + Metric.ball 0 δ) f) :
    ∃ L : ℝ, ∀ y ∈ K, ∀ z ∈ K, |f y - f z| ≤ L * ‖y - z‖ := by
  have hO : IsOpen (K + Metric.ball (0 : E) δ) := Metric.isOpen_ball.add_left
  have hcont : ContinuousOn f (K + Metric.ball 0 δ) := hf.continuousOn hO
  have hK' : IsCompact (K + Metric.closedBall (0 : E) (3 * δ / 4)) :=
    hK.add (isCompact_closedBall _ _)
  have hK'O : K + Metric.closedBall (0 : E) (3 * δ / 4) ⊆ K + Metric.ball 0 δ :=
    Set.add_subset_add_left (Metric.closedBall_subset_ball (by linarith))
  obtain ⟨M, hM⟩ := hK'.exists_bound_of_continuousOn (hcont.mono hK'O)
  set M' := max M 0 with hM'
  have hmemK' : ∀ y ∈ K, ∀ a : E, dist a y ≤ 3 * δ / 4 →
      a ∈ K + Metric.closedBall (0 : E) (3 * δ / 4) := by
    intro y hy a ha
    refine ⟨y, hy, a - y, ?_, by simp⟩
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact ha
  have hbd : ∀ y ∈ K, ∀ a : E, dist a y ≤ 3 * δ / 4 → |f a| ≤ M' := by
    intro y hy a ha
    have := hM a (hmemK' y hy a ha)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  refine ⟨8 * M' / δ, fun y hy z hz => ?_⟩
  have hM'0 : 0 ≤ M' := le_max_right _ _
  by_cases hyz : ‖y - z‖ < δ / 2
  · have hball : Metric.ball y (3 * δ / 4) ⊆ K + Metric.ball 0 δ := by
      intro a ha
      refine ⟨y, hy, a - y, ?_, by simp⟩
      rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
      have := Metric.mem_ball.1 ha
      linarith
    have hconv := hf.subset hball (convex_ball y _)
    have hL := hconv.lipschitzOnWith_of_abs_le (ε := δ / 4) (by positivity)
      (fun a ha => hbd y hy a ha.le)
    have hyb : y ∈ Metric.ball y (3 * δ / 4 - δ / 4) := Metric.mem_ball_self (by linarith)
    have hzb : z ∈ Metric.ball y (3 * δ / 4 - δ / 4) := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
      linarith
    have := hL.dist_le_mul y hyb z hzb
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)] at this
    calc |f y - f z| ≤ 2 * M' / (δ / 4) * ‖y - z‖ := this
      _ = 8 * M' / δ * ‖y - z‖ := by field_simp; ring
  · replace hyz := not_lt.1 hyz
    have hy' : |f y| ≤ M' := hbd y hy y (by simp; positivity)
    have hz' : |f z| ≤ M' := hbd z hz z (by simp; positivity)
    have h1 : |f y - f z| ≤ |f y| + |f z| := abs_sub _ _
    have h2 : 8 * M' / δ * (δ / 2) ≤ 8 * M' / δ * ‖y - z‖ :=
      mul_le_mul_of_nonneg_left hyz (by positivity)
    have h3 : 8 * M' / δ * (δ / 2) = 4 * M' := by field_simp; ring
    linarith

lemma lower_bound {E : Type*} [NormedAddCommGroup E] (V : E → EReal) (X : Set E)
    (hX : IsCompact X) (hout : ∀ z ∉ X, V z = ⊤) (hfin : ∀ z ∈ X, V z ≠ ⊤ ∧ V z ≠ ⊥) (L : ℝ)
    (hL : ∀ y ∈ X, ∀ z ∈ X, |(V y).toReal - (V z).toReal| ≤ L * ‖y - z‖) :
    ∃ b : ℝ, ∀ z, (b : EReal) ≤ V z := by
  by_cases hne : X.Nonempty
  · obtain ⟨z0, hz0⟩ := hne
    obtain ⟨R, hR⟩ := hX.isBounded.subset_closedBall z0
    refine ⟨(V z0).toReal - |L| * |R|, fun z => ?_⟩
    by_cases hz : z ∈ X
    · rw [← EReal.coe_toReal (hfin z hz).1 (hfin z hz).2, EReal.coe_le_coe_iff]
      have h1 := abs_le.1 (hL z hz z0 hz0)
      have h2 : ‖z - z0‖ ≤ |R| := by
        rw [← dist_eq_norm]
        exact (Metric.mem_closedBall.1 (hR hz)).trans (le_abs_self R)
      have h3 : L * ‖z - z0‖ ≤ |L| * |R| :=
        (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg L))
      linarith
    · rw [hout z hz]
      exact le_top
  · refine ⟨0, fun z => ?_⟩
    have hz : z ∉ X := fun h => hne ⟨z, h⟩
    rw [hout z hz]
    exact le_top

lemma mul_ne_bot_of_nonneg {c : ℝ} (hc : 0 ≤ c) {x : EReal} (hx : x ≠ ⊥) :
    (c : EReal) * x ≠ ⊥ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | coe x => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  | top =>
    rcases hc.eq_or_lt with h | h
    · subst h; simp
    · rw [EReal.coe_mul_top_of_pos h]; simp

lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

open ConvexSDDP.Stoch

variable {H : ℕ} {T : Tree H} {d p : ℕ}

lemma stage_child {n m : T.Node} (hm : m ∈ T.children n) :
    (T.stage m).val = (T.stage n).val + 1 ∧ T.anc m = n := by
  simpa [Tree.children] using hm

lemma ne_root_of_child {n m : T.Node} (hm : m ∈ T.children n) : m ≠ T.root := by
  intro h
  have := (stage_child hm).1
  rw [h, T.root_stage] at this
  omega

lemma stage_lt_card (T : Tree H) (m : T.Node) : (T.stage m).val < Fintype.card T.Node := by
  have hst : ∀ i ≤ (T.stage m).val, (T.stage (T.anc^[i] m)).val = (T.stage m).val - i := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have h1 := ih (by omega)
      have h2 := T.anc_stage (T.anc^[i] m) (by omega)
      omega
  let g : Fin ((T.stage m).val + 1) → T.Node := fun i => T.anc^[i.val] m
  have hg : Function.Injective g := by
    intro i j hij
    have := congrArg (fun z => (T.stage z).val) hij
    simp only [g] at this
    have hi := i.isLt
    have hj := j.isLt
    rw [hst i (by omega), hst j (by omega)] at this
    ext
    omega
  have := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at this
  omega

lemma fuel_stable (M : Model T d p) : ∀ s, ∀ m : T.Node,
    Fintype.card T.Node - (T.stage m).val ≤ s →
    ∀ h, Fintype.card T.Node ≤ h + (T.stage m).val → M.Vfuel (h + 1) m = M.Vfuel h m := by
  intro s
  induction s with
  | zero => intro m hs; have := stage_lt_card T m; omega
  | succ s ih =>
    intro m hs h hh
    have hlt := stage_lt_card T m
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    funext z
    rw [Model.Vfuel.eq_2 M m z (h' + 1), Model.Vfuel.eq_2 M m z h']
    split_ifs with hz hl
    · rfl
    · apply Finset.sum_congr rfl
      intro c hc
      have hcs := (stage_child hc).1
      rw [ih c (by omega) h' (by omega)]
    · rfl


open Classical in
lemma V_eq (M : Model T d p) (n : T.Node) (z : EuclideanSpace ℝ (Fin d)) :
    M.V n z = if z ∈ M.X n then (if IsLeaf T n then M.VL n z else
      ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
        ⨅ u ∈ M.U m z, (M.C m z u + M.V m (M.f m (z, u)))) else ⊤ := by
  have hcard : Fintype.card T.Node = (Fintype.card T.Node - 1) + 1 := by
    have : 0 < Fintype.card T.Node := Fintype.card_pos_iff.mpr ⟨T.root⟩
    omega
  have eV : M.V n z = M.Vfuel ((Fintype.card T.Node - 1) + 1) n z := by
    unfold Model.V; rw [← hcard]
  rw [eV, Model.Vfuel.eq_2]
  split_ifs with h1 h2
  · rfl
  · apply Finset.sum_congr rfl
    intro m hm
    have hst := (stage_child hm).1
    have hfs : M.Vfuel (Fintype.card T.Node - 1) m = M.V m := by
      unfold Model.V
      have := stage_lt_card T m
      conv_rhs => rw [hcard]
      exact (fuel_stable M _ m le_rfl _ (by omega)).symm
    rw [hfs]
  · rfl


lemma ut_convex (M : Model T d p) (hH2 : M.H2) (m : T.Node) (hm : m ≠ T.root) :
    ConvexMultifunction (M.Ut m) := by
  intro x y a ha b hb l hl0 hl1
  refine ⟨(hH2.2.2.2.1 m hm).1 x y a ha.1 b hb.1 l hl0 hl1, ?_⟩
  have e : M.f m ((1 - l) • x + l • y, (1 - l) • a + l • b) =
      (1 - l) • M.f m (x, a) + l • M.f m (y, b) := by
    rw [← map_smul, ← map_smul, ← map_add]
    rfl
  rw [e]
  exact (hH2.2.2.1 m).1 ha.2 hb.2 (by linarith) hl0.le (by ring)

lemma vtilde_bound (M : Model T d p) (hH2 : M.H2) (n : T.Node) (hn : ¬ IsLeaf T n) :
    ∃ Mb : ℝ, ∀ y ∈ M.X n + Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (M.δ / 2),
      M.Vtilde n y ≤ (Mb : EReal) := by
  classical
  have h31i := lemma_3_1_i M hH2
  have hH2' := hH2
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8⟩ := hH2'
  have hΦ : ∀ m, 0 < M.Φ m := hA1.1
  have hout : ∀ m z, z ∉ M.X m → M.V m z = ⊤ := by
    intro m z hz
    rw [V_eq, if_neg hz]
  have hVb : ∀ m z, M.V m z ≠ ⊥ := by
    intro m z
    by_cases hz : z ∈ M.X m
    · exact ((h31i m).2.1 z hz).2
    · rw [hout m z hz]; simp
  let φ : T.Node → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) → EReal :=
    fun m q => M.C m q.1 q.2 + M.V m (M.f m q)
  let h : T.Node → EuclideanSpace ℝ (Fin d) → EReal :=
    fun m z => ⨅ u ∈ M.Ut m z, φ m (z, u)
  have hne : ∀ m ∈ T.children n, m ≠ T.root := fun m hm => ne_root_of_child hm
  have hφc : ∀ m ∈ T.children n, ConvexSDDP.Det.EConvex (φ m) := by
    intro m hm
    exact econvex_add _ _ (hA5 m (hne m hm)).1.1 (fun q => hVb _ _) (hA5 m (hne m hm)).2.2
      (econvex_comp_linear (M.V m) (h31i m).1 (M.f m))
  have hhc : ∀ m ∈ T.children n, ConvexSDDP.Det.EConvex (h m) := fun m hm =>
    econvex_pinf (M.Ut m) (ut_convex M hH2 m (hne m hm)) (φ m) (hφc m hm)
  have hhb : ∀ m ∈ T.children n, ∀ z, h m z ≠ ⊥ := by
    intro m hm z
    obtain ⟨-, hfin, L, hL⟩ := h31i m
    obtain ⟨b, hb⟩ := lower_bound (M.V m) (M.X m) (hA3 m).2 (hout m) hfin L hL
    have hmono : ⨅ u ∈ M.U m z, φ m (z, u) ≤ h m z := biInf_mono (fun u hu => hu.1)
    by_cases hUne : (M.U m z).Nonempty
    · have hlsc : LowerSemicontinuousOn (fun u => M.C m z u) (M.U m z) := by
        have := (hA5 m (hne m hm)).2.1.comp (continuous_const.prodMk continuous_id
          (f := fun _ : EuclideanSpace ℝ (Fin p) => z))
        exact this.lowerSemicontinuousOn _
      obtain ⟨u0, -, hu0⟩ := hlsc.exists_isMinOn hUne ((hA4 m (hne m hm)).2 z).2
      have hle : M.C m z u0 + (b : EReal) ≤ h m z := by
        refine le_trans ?_ hmono
        apply le_iInf₂
        intro u hu
        exact add_le_add (hu0 hu) (hb _)
      intro hbot
      rw [hbot, le_bot_iff] at hle
      exact EReal.add_ne_bot_iff.2 ⟨(hA5 m (hne m hm)).1.1 (z, u0), EReal.coe_ne_bot b⟩ hle
    · rw [Set.not_nonempty_iff_eq_empty] at hUne
      intro hbot
      have : ⨅ u ∈ M.U m z, φ m (z, u) = ⊤ := by simp [hUne]
      rw [this, hbot] at hmono
      exact absurd hmono (by simp)
  set O := M.X n + Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M.δ with hOdef
  have hht : ∀ m ∈ T.children n, ∀ z ∈ O, h m z ≠ ⊤ := by
    intro m hm z hz
    obtain ⟨⟨u, hu, hfu⟩, hCt⟩ := hA8.2 n hn z hz m hm
    have : h m z ≤ φ m (z, u) := biInf_le (fun u => φ m (z, u)) (show u ∈ M.Ut m z from ⟨hu, hfu⟩)
    refine ne_top_of_le_ne_top ?_ this
    exact EReal.add_ne_top (hCt u hu).ne ((h31i m).2.1 _ hfu).1
  have hwn : ∀ m, 0 ≤ M.Φ m / M.Φ n := fun m => div_nonneg (hΦ m).le (hΦ n).le
  let G : EuclideanSpace ℝ (Fin d) → EReal :=
    fun z => ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) * h m z
  have hGV : ∀ z, M.Vtilde n z = G z := fun z => rfl
  obtain ⟨hGc, -⟩ := econvex_sum (T.children n)
    (fun m z => ((M.Φ m / M.Φ n : ℝ) : EReal) * h m z)
    (fun m hm z => mul_ne_bot_of_nonneg (hwn m) (hhb m hm z))
    (fun m hm => econvex_smul _ (hwn m) _ (hhb m hm) (hhc m hm))
  have hGreal : ∀ z ∈ O, G z = ((∑ m ∈ T.children n,
      (M.Φ m / M.Φ n) * (h m z).toReal : ℝ) : EReal) := by
    intro z hz
    rw [coe_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [EReal.coe_mul, EReal.coe_toReal (hht m hm z hz) (hhb m hm z)]
  have hOc : Convex ℝ O := (hA3 n).1.add (convex_ball _ _)
  have hconvOn : ConvexOn ℝ O (fun z => (G z).toReal) := by
    refine ⟨hOc, fun x hx y hy a b ha hb hab => ?_⟩
    have hb1 : b ≤ 1 := by linarith
    have ha' : a = 1 - b := by linarith
    subst ha'
    have hGx := hGreal x hx
    have hGy := hGreal y hy
    have := (econvex_iff G).1 hGc x y (G x).toReal (G y).toReal
      (by rw [hGx, EReal.toReal_coe]) (by rw [hGy, EReal.toReal_coe]) b hb hb1
    have hz : (1 - b) • x + b • y ∈ O := hOc hx hy ha hb hab
    have this' : G ((1 - b) • x + b • y) ≤
        (((1 - b) * (G x).toReal + b * (G y).toReal : ℝ) : EReal) := this
    rw [hGreal _ hz, EReal.coe_le_coe_iff] at this'
    show (G ((1 - b) • x + b • y)).toReal ≤ (1 - b) * (G x).toReal + b * (G y).toReal
    rw [hGreal _ hz, EReal.toReal_coe]
    exact this'
  have hO : IsOpen O := Metric.isOpen_ball.add_left
  have hcont := hconvOn.continuousOn hO
  have hK' : IsCompact (M.X n + Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (M.δ / 2)) :=
    (hA3 n).2.add (isCompact_closedBall _ _)
  have hK'O : M.X n + Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (M.δ / 2) ⊆ O :=
    Set.add_subset_add_left (Metric.closedBall_subset_ball (by linarith [hA8.1]))
  obtain ⟨Mb, hMb⟩ := hK'.exists_bound_of_continuousOn (hcont.mono hK'O)
  refine ⟨Mb, fun y hy => ?_⟩
  rw [hGV, hGreal y (hK'O hy), EReal.coe_le_coe_iff]
  have := hMb y hy
  rw [Real.norm_eq_abs, hGreal y (hK'O hy), EReal.toReal_coe] at this
  exact (le_abs_self _).trans this

lemma coe_max' (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.2 h)]
  · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.2 h)]

end SolL31iii

open ConvexSDDP.Stoch SolL31iii in
theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) :
    ∀ n, ¬ IsLeaf T n → ∃ α : ℝ, 0 ≤ α ∧
      (∀ k, r.θ k n ≠ ⊥ → ‖r.β k n‖ ≤ α) ∧
      ∀ k y z, r.Vc k n y ≠ ⊥ →
        (r.Vc k n z ≠ ⊥ ∧ |(r.Vc k n y).toReal - (r.Vc k n z).toReal| ≤ α * ‖y - z‖) := by
  classical
  intro n hn
  have h31i := lemma_3_1_i M hH2
  have h31ii := lemma_3_1_ii M hH2 R ys r hr
  have h26 := eq_26 M hH2 R ys r hr
  have hxX : ∀ k m, r.x k m ∈ M.X m := by
    intro k m
    by_cases hroot : m = T.root
    · rw [hroot, hr.2.2.1 k]
      exact hH2.2.1
    · obtain ⟨-, hu, -, hx⟩ := hr.2.2.2.1 k m hroot
      rw [hx]
      exact hu.2
  have hδ : 0 < M.δ := hH2.2.2.2.2.2.2.2.1
  obtain ⟨Mb, hMb⟩ := vtilde_bound M hH2 n hn
  have hupd : ∀ k y, r.Vc (k + 1) n y = max (r.Vc k n y)
      (r.θ k n + ((inner ℝ (r.β k n) (y - r.x k n) : ℝ) : EReal)) := fun k y => by
    rw [hr.2.2.2.2.2.2 k n hn]
  have hmono : ∀ i j, i ≤ j → ∀ y, r.Vc i n y ≤ r.Vc j n y := by
    intro i j hij y
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (by rw [hupd]; exact le_max_left _ _)
  have hθtop : ∀ k, r.θ k n ≠ ⊤ := by
    intro k
    rw [← (h26 k n hn).1]
    have hx := hxX k n
    exact ne_top_of_le_ne_top ((h31i n).2.1 _ hx).1
      (((h31ii (k + 1) n hn).1 _ (subset_affineSpan ℝ _ hx)).trans ((h31ii (k + 1) n hn).2 _))
  have hcut : ∀ k, ∀ y ∈ affineSpan ℝ (M.X n),
      r.θ k n + ((inner ℝ (r.β k n) (y - r.x k n) : ℝ) : EReal) ≤ M.Vtilde n y := by
    intro k y hy
    refine le_trans ?_ ((h31ii (k + 1) n hn).1 y hy)
    rw [hupd]
    exact le_max_right _ _
  obtain ⟨Rd, hRd⟩ := Metric.isBounded_iff.1 (hH2.2.2.1 n).2.isBounded
  by_cases hex : ∃ k, r.θ k n ≠ ⊥
  swap
  · have hex' : ∀ k, r.θ k n = ⊥ := fun k => by
      by_contra h
      exact hex ⟨k, h⟩
    refine ⟨0, le_rfl, fun k hk => absurd (hex' k) hk, ?_⟩
    have hbot : ∀ k y, r.Vc k n y = ⊥ := by
      intro k
      induction k with
      | zero => intro y; rw [hr.1 n hn]
      | succ k ih => intro y; rw [hupd, ih, hex' k, EReal.bot_add]; simp
    intro k y z hy
    exact absurd (hbot k y) hy
  set k0 := Nat.find hex with hk0def
  have hk0 : r.θ k0 n ≠ ⊥ := Nat.find_spec hex
  set θ0 := (r.θ k0 n).toReal with hθ0def
  have hθ0 : r.θ k0 n = (θ0 : EReal) := (EReal.coe_toReal (hθtop k0) hk0).symm
  set Lb := θ0 - ‖r.β k0 n‖ * Rd with hLb
  have hlow : ∀ k, r.θ k n ≠ ⊥ → (Lb : EReal) ≤ r.θ k n := by
    intro k hk
    have hk0k : k0 ≤ k := Nat.find_min' hex hk
    rw [← (h26 k n hn).1]
    refine le_trans ?_ (hmono (k0 + 1) (k + 1) (by omega) _)
    rw [hupd]
    refine le_trans ?_ (le_max_right _ _)
    rw [hθ0, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have h1 := abs_le.1 (abs_real_inner_le_norm (r.β k0 n) (r.x k n - r.x k0 n))
    have h2 : ‖r.x k n - r.x k0 n‖ ≤ Rd := by
      rw [← dist_eq_norm]; exact hRd (hxX k n) (hxX k0 n)
    have h3 : ‖r.β k0 n‖ * ‖r.x k n - r.x k0 n‖ ≤ ‖r.β k0 n‖ * Rd :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    rw [hLb]
    linarith [h1.1]
  set α := max (2 * (Mb - Lb) / M.δ) 0 with hαdef
  have hsel : ∀ k, ys k n = true → r.θ k n ≠ ⊥ → ‖r.β k n‖ ≤ α := by
    intro k hys hk
    obtain ⟨-, hβ⟩ := (hr.2.2.2.2.2.1 k n hn).1 hys
    have hβmem : r.β k n ∈ vectorSpan ℝ (M.X n) := by
      rw [hβ]
      refine Submodule.sum_mem _ (fun m hm => Submodule.smul_mem _ _ ?_)
      have hne := ne_root_of_child hm
      have hanc := (stage_child hm).2
      have := (hr.2.2.2.2.1 k m hne (by rw [hanc]; exact hys)).2.2.1
      rw [hanc] at this
      exact this
    by_cases hβ0 : r.β k n = 0
    · rw [hβ0, norm_zero]; exact le_max_right _ _
    have hβpos : 0 < ‖r.β k n‖ := norm_pos_iff.2 hβ0
    set x := r.x k n with hxdef
    set c := M.δ / (2 * ‖r.β k n‖) with hcdef
    set y := c • r.β k n + x with hydef
    have hy_aff : y ∈ affineSpan ℝ (M.X n) := by
      have := AffineSubspace.vadd_mem_of_mem_direction (s := affineSpan ℝ (M.X n))
        (v := c • r.β k n) (by rw [direction_affineSpan]; exact Submodule.smul_mem _ _ hβmem)
        (subset_affineSpan ℝ _ (hxX k n))
      simpa [vadd_eq_add] using this
    have hy_K : y ∈ M.X n + Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (M.δ / 2) := by
      refine ⟨x, hxX k n, c • r.β k n, ?_, by rw [hydef, add_comm]⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      rw [hcdef]
      field_simp
      rfl
    have h1 := (hcut k y hy_aff).trans (hMb y hy_K)
    have hin : inner ℝ (r.β k n) (y - x) = M.δ / 2 * ‖r.β k n‖ := by
      rw [hydef, add_sub_cancel_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hcdef]
      field_simp
    rw [hin] at h1
    have hθr := EReal.coe_toReal (hθtop k) hk
    rw [← hθr, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    have hl := hlow k hk
    rw [← hθr, EReal.coe_le_coe_iff] at hl
    have h2 : M.δ / 2 * ‖r.β k n‖ ≤ Mb - Lb := by linarith
    refine le_trans ?_ (le_max_left _ _)
    rw [le_div_iff₀ hδ]
    linarith
  -- slope bound given the structure of Vc k
  have hβ_of : ∀ k, ((∀ y, r.Vc k n y = ⊥) ∨ ((∀ y, r.Vc k n y ≠ ⊥ ∧ r.Vc k n y ≠ ⊤) ∧
      ∀ y z, |(r.Vc k n y).toReal - (r.Vc k n z).toReal| ≤ α * ‖y - z‖)) →
      r.θ k n ≠ ⊥ → ‖r.β k n‖ ≤ α := by
    intro k hcl hk
    cases hys : ys k n with
    | true => exact hsel k hys hk
    | false =>
      obtain ⟨hθ, -, hsub⟩ := (hr.2.2.2.2.2.1 k n hn).2 hys
      rcases hcl with hbot | ⟨hfin, hlip⟩
      · exact absurd (hθ.trans (hbot _)) hk
      by_cases hβ0 : r.β k n = 0
      · rw [hβ0, norm_zero]; exact le_max_right _ _
      have hβpos : 0 < ‖r.β k n‖ := norm_pos_iff.2 hβ0
      set x := r.x k n
      set y := (1 / ‖r.β k n‖) • r.β k n + x with hydef
      have h1 := hsub y
      have hin : inner ℝ (r.β k n) (y - x) = ‖r.β k n‖ := by
        rw [hydef, add_sub_cancel_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [hin, hθ] at h1
      have ex := EReal.coe_toReal (hfin x).2 (hfin x).1
      have ey := EReal.coe_toReal (hfin y).2 (hfin y).1
      rw [← ex, ← ey, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      have h2 := abs_le.1 (hlip y x)
      have h3 : ‖y - x‖ = 1 := by
        rw [hydef, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
      rw [h3] at h2
      linarith [h2.1, h2.2]
  have claim : ∀ k, (∀ y, r.Vc k n y = ⊥) ∨ ((∀ y, r.Vc k n y ≠ ⊥ ∧ r.Vc k n y ≠ ⊤) ∧
      ∀ y z, |(r.Vc k n y).toReal - (r.Vc k n z).toReal| ≤ α * ‖y - z‖) := by
    intro k
    induction k with
    | zero => left; intro y; rw [hr.1 n hn]
    | succ k ih =>
      have hβk := hβ_of k ih
      by_cases hθ : r.θ k n = ⊥
      · have e : ∀ y, r.Vc (k + 1) n y = r.Vc k n y := fun y => by
          rw [hupd, hθ, EReal.bot_add]
          exact max_bot_right _
        simp only [e]
        exact ih
      · right
        set θr := (r.θ k n).toReal with hθrdef
        have hθr : r.θ k n = (θr : EReal) := (EReal.coe_toReal (hθtop k) hθ).symm
        have hb := hβk hθ
        set aff : EuclideanSpace ℝ (Fin d) → ℝ :=
          fun y => θr + inner ℝ (r.β k n) (y - r.x k n) with haffdef
        have hcutE : ∀ y, r.θ k n + ((inner ℝ (r.β k n) (y - r.x k n) : ℝ) : EReal) =
            ((aff y : ℝ) : EReal) := by
          intro y
          rw [hθr, ← EReal.coe_add]
        have hafflip : ∀ y z, |aff y - aff z| ≤ α * ‖y - z‖ := by
          intro y z
          have e : aff y - aff z = inner ℝ (r.β k n) (y - z) := by
            show (θr + inner ℝ (r.β k n) (y - r.x k n)) -
              (θr + inner ℝ (r.β k n) (z - r.x k n)) = _
            rw [← sub_sub_sub_cancel_right y z (r.x k n),
              inner_sub_right (r.β k n) (y - r.x k n) (z - r.x k n)]
            ring
          rw [e]
          exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
        rcases ih with hbot | ⟨hfin, hlip⟩
        · have e : ∀ y, r.Vc (k + 1) n y = ((aff y : ℝ) : EReal) := fun y => by
            rw [hupd, hbot, hcutE]
            exact max_eq_right bot_le
          refine ⟨fun y => ?_, fun y z => ?_⟩
          · rw [e]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
          · rw [e, e, EReal.toReal_coe, EReal.toReal_coe]; exact hafflip y z
        · have e : ∀ y, r.Vc (k + 1) n y =
              ((max (r.Vc k n y).toReal (aff y) : ℝ) : EReal) := fun y => by
            rw [hupd, hcutE, coe_max', EReal.coe_toReal (hfin y).2 (hfin y).1]
          refine ⟨fun y => ?_, fun y z => ?_⟩
          · rw [e]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
          · rw [e, e, EReal.toReal_coe, EReal.toReal_coe]
            refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hlip y z) (hafflip y z))
  refine ⟨α, le_max_right _ _, fun k hk => hβ_of k (claim k) hk, fun k y z hy => ?_⟩
  rcases claim k with hbot | ⟨hfin, hlip⟩
  · exact absurd (hbot y) hy
  · exact ⟨(hfin z).1, hlip y z⟩
