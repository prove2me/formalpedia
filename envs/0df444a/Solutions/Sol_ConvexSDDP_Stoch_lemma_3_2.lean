-- Prove2me | solution 1 for ConvexSDDP.Stoch.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:57:54.515812+00:00
-- url     : https://prove2.me/submissions/3e39365e-f613-49f3-a945-2807f8667110

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_i
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_ii
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_iii
open StochasticProg.Multistage MeasureTheory Filter Topology
open scoped Pointwise

namespace Sol32
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

lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

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

lemma tendsto_of_finite (a : ℕ → EReal) (h0 : ∀ k, 0 ≤ a k)
    (hfin : ∀ ε : ℝ, 0 < ε → {k | (ε : EReal) ≤ a k}.Finite) : Tendsto a atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    exact Eventually.of_forall fun k => lt_of_lt_of_le hb (h0 k)
  · intro b hb
    obtain ⟨ε', hε'0, hε'b⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    have hε'0' : (0 : ℝ) < ε' := by exact_mod_cast hε'0
    have hev := (hfin ε' hε'0').eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at hev
    filter_upwards [hev] with k hk
    simp only [not_le] at hk
    exact hk.trans hε'b

lemma ereal_fin_sub {a b : EReal} (ha : a ≠ ⊤) (ha' : a ≠ ⊥) (hb : b ≠ ⊤) (hb' : b ≠ ⊥) :
    a - b = ((a.toReal - b.toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_toReal ha ha', EReal.coe_toReal hb hb']

/-- Deterministic part: exactness along the selected blocks with respect to `F (kτ+1)` implies
exactness along the selected blocks with respect to `F (kτ)` (compactness and Lipschitz). -/
lemma step1 {E : Type*} [NormedAddCommGroup E] (K : Set E) (hK : IsCompact K) (x : ℕ → E)
    (hx : ∀ k, x k ∈ K) (f : E → EReal) (F : ℕ → E → EReal)
    (hf : ∀ y ∈ K, f y ≠ ⊤ ∧ f y ≠ ⊥) (L : ℝ)
    (hL : ∀ y ∈ K, ∀ z ∈ K, |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖)
    (α : ℝ) (hα : ∀ k y z, F k y ≠ ⊥ → F k z ≠ ⊥ ∧ |(F k y).toReal - (F k z).toReal| ≤ α * ‖y - z‖)
    (hmono : ∀ i j, i ≤ j → ∀ y, F i y ≤ F j y) (hle : ∀ k, ∀ y ∈ K, F k y ≤ f y)
    (τ : ℕ) (hτ : 0 < τ) (S : Set ℕ)
    (hg : Tendsto (fun k => f (x k) - F (k * τ + 1) (x k)) (atTop ⊓ 𝓟 S) (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    {k | (ε : EReal) ≤ f (x k) - F (k * τ) (x k) ∧ k ∈ S}.Finite := by
  by_contra hinf
  let pr : ℕ → Prop := fun k => (ε : EReal) ≤ f (x k) - F (k * τ) (x k) ∧ k ∈ S
  have hinf' : (Set.ofPred pr).Infinite := hinf
  have hφ : StrictMono (Nat.nth pr) := Nat.nth_strictMono hinf'
  have hφI : ∀ i, pr (Nat.nth pr i) := Nat.nth_mem_of_infinite hinf'
  obtain ⟨a, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq (fun i => hx (Nat.nth pr i))
  have hc : StrictMono (fun i => Nat.nth pr (ψ i)) := hφ.comp hψ
  set A := |L| + |α| with hAdef
  have hA : 0 ≤ A := by positivity
  set δ := ε / (2 * (A + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have h1 : ∀ᶠ i in atTop, dist (x (Nat.nth pr (ψ i))) a < δ / 2 :=
    (Metric.tendsto_nhds.1 hlim) _ (by positivity)
  have h2 : ∀ᶠ i in atTop, f (x (Nat.nth pr (ψ i))) - F (Nat.nth pr (ψ i) * τ + 1)
      (x (Nat.nth pr (ψ i))) < ((ε / 2 : ℝ) : EReal) := by
    have h := (tendsto_order.1 hg).2 ((ε / 2 : ℝ) : EReal)
      (by exact_mod_cast (by positivity : (0 : ℝ) < ε / 2))
    rw [eventually_inf_principal] at h
    have h' := hc.tendsto_atTop.eventually h
    filter_upwards [h'] with i hi using hi (hφI (ψ i)).2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and h2)
  obtain ⟨hd1, hg1⟩ := hN N le_rfl
  obtain ⟨hd2, -⟩ := hN (N + 1) (by omega)
  have hk : Nat.nth pr (ψ N) < Nat.nth pr (ψ (N + 1)) := hc (by omega)
  have hbad := (hφI (ψ (N + 1))).1
  set k1 := Nat.nth pr (ψ N) with hk1
  set k2 := Nat.nth pr (ψ (N + 1)) with hk2
  set x1 := x k1
  set x2 := x k2
  have hx1 : x1 ∈ K := hx k1
  have hx2 : x2 ∈ K := hx k2
  have hdist : ‖x1 - x2‖ < δ := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right x1 x2 a]
  obtain ⟨hf1t, hf1b⟩ := hf x1 hx1
  obtain ⟨hf2t, hf2b⟩ := hf x2 hx2
  have hb1 : F (k1 * τ + 1) x1 ≠ ⊥ := by
    intro hb
    rw [hb, EReal.sub_bot hf1b] at hg1
    exact absurd hg1 (not_lt.2 le_top)
  obtain ⟨hb2, hlip⟩ := hα (k1 * τ + 1) x1 x2 hb1
  have hkk : k1 * τ + 1 ≤ k2 * τ := by
    have : (k1 + 1) * τ ≤ k2 * τ := Nat.mul_le_mul_right τ hk
    nlinarith
  have hmon : F (k1 * τ + 1) x2 ≤ F (k2 * τ) x2 := hmono _ _ hkk x2
  have hc2b : F (k2 * τ) x2 ≠ ⊥ := fun h => hb2 (le_bot_iff.1 (h ▸ hmon))
  have hc2t : F (k2 * τ) x2 ≠ ⊤ := ne_top_of_le_ne_top hf2t (hle _ x2 hx2)
  have hb1t : F (k1 * τ + 1) x1 ≠ ⊤ := ne_top_of_le_ne_top hf1t (hle _ x1 hx1)
  have hb2t : F (k1 * τ + 1) x2 ≠ ⊤ := ne_top_of_le_ne_top hf2t (hle _ x2 hx2)
  rw [ereal_fin_sub hf1t hf1b hb1t hb1, EReal.coe_lt_coe_iff] at hg1
  rw [ereal_fin_sub hf2t hf2b hc2t hc2b, EReal.coe_le_coe_iff] at hbad
  have hmon' := EReal.toReal_le_toReal hmon hb2 hc2t
  have hLx := abs_le.1 (hL x2 hx2 x1 hx1)
  have hlip' := abs_le.1 hlip
  have e0 : ‖x2 - x1‖ = ‖x1 - x2‖ := norm_sub_rev _ _
  have e1 : L * ‖x2 - x1‖ ≤ |L| * δ := by
    rw [e0]
    exact (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hdist.le (abs_nonneg L))
  have e2 : α * ‖x1 - x2‖ ≤ |α| * δ :=
    (mul_le_mul_of_nonneg_right (le_abs_self α) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hdist.le (abs_nonneg α))
  have e3 : A * δ < ε / 2 := by
    rw [hδdef, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e4 : |L| * δ + |α| * δ = A * δ := by rw [hAdef]; ring
  linarith

end Sol32

open ConvexSDDP.Stoch Sol32 in
theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) (ys : ℕ → T.Node → Bool) (r : RunData T d p)
    (hr : IsTreeRun M R ys r) (n : T.Node) (hn : ¬ IsLeaf T n) (τ' : ℕ) (hτ' : 0 < τ')
    (hch : ∀ m ∈ T.children n,
      Tendsto (fun k => M.V m (r.x (k * τ') m) - r.Vc (k * τ' + 1) m (r.x (k * τ') m))
        atTop (𝓝 0)) :
    Tendsto (fun k => (∑ m ∈ T.children n,
        ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m (r.x (k * τ') n) (r.u (k * τ') m)) -
        M.V n (r.x (k * τ') n)) atTop (𝓝 0) := by
  classical
  have hΦ : ∀ m, 0 < M.Φ m := hH2.1.1
  have hw : ∀ m : T.Node, (0 : EReal) ≤ ((M.Φ m / M.Φ n : ℝ) : EReal) := fun m =>
    EReal.coe_nonneg.mpr (div_nonneg (hΦ m).le (hΦ n).le)
  have hwsum : ∑ m ∈ T.children n, (M.Φ m / M.Φ n) = 1 := by
    rw [← Finset.sum_div, hH2.1.2.2 n hn, div_self (hΦ n).ne']
  have hxX : ∀ k m, r.x k m ∈ M.X m := by
    intro k m
    by_cases hroot : m = T.root
    · rw [hroot, hr.2.2.1 k]
      exact hH2.2.1
    · obtain ⟨-, hu, -, hx⟩ := hr.2.2.2.1 k m hroot
      rw [hx]
      exact hu.2
  have h31i := lemma_3_1_i M hH2
  have h31ii := lemma_3_1_ii M hH2 R ys r hr
  have hVcV : ∀ k m, ∀ z ∈ M.X m, r.Vc k m z ≤ M.V m z := by
    intro k m z hz
    by_cases hm : IsLeaf T m
    · rw [hr.2.1 k m hm]
    · exact ((h31ii k m hm).1 z (subset_affineSpan ℝ _ hz)).trans ((h31ii k m hm).2 z)
  -- Lemma 5.2: exactness w.r.t. the previous approximation at the children
  have hgap : ∀ m ∈ T.children n, Tendsto (fun k => M.V m (r.x (k * τ') m) -
      r.Vc (k * τ') m (r.x (k * τ') m)) atTop (𝓝 0) := by
    intro m hm
    obtain ⟨-, hVfin, L, hL⟩ := h31i m
    by_cases hml : IsLeaf T m
    · have : ∀ k, M.V m (r.x (k * τ') m) - r.Vc (k * τ') m (r.x (k * τ') m) = 0 := fun k => by
        rw [hr.2.1 _ m hml]
        exact EReal.sub_self (hVfin _ (hxX _ _)).1 (hVfin _ (hxX _ _)).2
      simp only [this]
      exact tendsto_const_nhds
    · obtain ⟨α, -, -, hα⟩ := lemma_3_1_iii M hH2 R ys r hr m hml
      have hmono : ∀ i j, i ≤ j → ∀ y, r.Vc i m y ≤ r.Vc j m y := by
        intro i j hij y
        induction hij with
        | refl => exact le_rfl
        | step _ ih =>
          refine ih.trans ?_
          rw [hr.2.2.2.2.2.2 _ m hml]
          exact le_max_left _ _
      apply tendsto_of_finite
      · intro k
        exact (EReal.sub_nonneg (Or.inl (hVfin _ (hxX _ _)).1) (Or.inl (hVfin _ (hxX _ _)).2)).2
          (hVcV _ m _ (hxX _ _))
      · intro ε hε
        have h1 := step1 (M.X m) (hH2.2.2.1 m).2 (fun k => r.x (k * τ') m) (fun k => hxX _ _)
          (M.V m) (fun k => r.Vc k m) hVfin L hL α hα hmono (fun k => hVcV k m) τ' hτ' Set.univ
          (by rw [principal_univ, inf_top_eq]; exact hch m hm) ε hε
        exact h1.subset (fun k hk => ⟨hk, Set.mem_univ _⟩)
  -- lower bound: V_n(x_n) ≤ Σ w W
  have hVle : ∀ j, M.V n (r.x j n) ≤ ∑ m ∈ T.children n,
      ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m (r.x j n) (r.u j m) := by
    intro j
    have hcard : Fintype.card T.Node = (Fintype.card T.Node - 1) + 1 := by
      have : 0 < Fintype.card T.Node := Fintype.card_pos_iff.mpr ⟨T.root⟩
      omega
    have eV : M.V n (r.x j n) = M.Vfuel ((Fintype.card T.Node - 1) + 1) n (r.x j n) := by
      unfold Model.V; rw [← hcard]
    rw [eV, Model.Vfuel.eq_2, if_pos (hxX j n), if_neg hn]
    apply Finset.sum_le_sum
    intro m hm
    apply mul_le_mul_of_nonneg_left _ (hw m)
    have hne := ne_root_of_child hm
    have hanc := (stage_child hm).2
    have hst := (stage_child hm).1
    obtain ⟨-, hu, -, -⟩ := hr.2.2.2.1 j m hne
    rw [hanc] at hu
    have hfs : M.Vfuel (Fintype.card T.Node - 1) m = M.V m := by
      unfold Model.V
      have := stage_lt_card T m
      conv_rhs => rw [hcard]
      exact (fuel_stable M _ m le_rfl _ (by omega)).symm
    rw [hfs]
    exact biInf_le (fun u => M.C m (r.x j n) u + M.V m (M.f m (r.x j n, u))) hu.1
  -- upper bound
  have hDle : ∀ k (ε' : ℝ), (∀ m ∈ T.children n, M.V m (r.x (k * τ') m) -
      r.Vc (k * τ') m (r.x (k * τ') m) < ε') →
      (∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m (r.x (k * τ') n)
        (r.u (k * τ') m)) - M.V n (r.x (k * τ') n) ≤ ε' := by
    intro k ε' hk
    set j := k * τ'
    set xn := r.x j n
    have hxn : xn ∈ M.X n := hxX j n
    obtain ⟨-, hVnfin, -⟩ := h31i n
    obtain ⟨hvt, hvb⟩ := hVnfin xn hxn
    have hδ := hH2.2.2.2.2.2.2.2
    have hxnb : xn ∈ M.X n + Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M.δ := by
      have := Set.add_mem_add hxn (Metric.mem_ball_self (x := (0 : EuclideanSpace ℝ (Fin d))) hδ.1)
      rwa [add_zero] at this
    -- finiteness facts
    have hfacts : ∀ m ∈ T.children n,
        M.C m xn (r.u j m) ≠ ⊤ ∧ M.C m xn (r.u j m) ≠ ⊥ ∧
        M.V m (r.x j m) ≠ ⊤ ∧ M.V m (r.x j m) ≠ ⊥ ∧
        r.Vc j m (r.x j m) ≠ ⊤ ∧ r.Vc j m (r.x j m) ≠ ⊥ ∧
        r.x j m = M.f m (xn, r.u j m) ∧ r.u j m ∈ M.Ut m xn ∧
        (∀ v ∈ M.Ut m xn, M.C m xn (r.u j m) + r.Vc j m (M.f m (xn, r.u j m)) ≤
          M.C m xn v + r.Vc j m (M.f m (xn, v))) := by
      intro m hm
      have hne := ne_root_of_child hm
      have hanc := (stage_child hm).2
      obtain ⟨-, hu, hmin, hx⟩ := hr.2.2.2.1 j m hne
      rw [hanc] at hu hmin hx
      obtain ⟨hbt, hbb⟩ := (h31i m).2.1 _ (hxX j m)
      have hcb : r.Vc j m (r.x j m) ≠ ⊥ := by
        intro h
        have := hk m hm
        rw [h, EReal.sub_bot hbb] at this
        exact absurd this (not_lt.2 le_top)
      refine ⟨((hδ.2 n hn xn hxnb m hm).2 _ hu.1).ne, (hH2.2.2.2.2.1 m hne).1.1 (xn, r.u j m),
        hbt, hbb, ne_top_of_le_ne_top hbt (hVcV j m _ (hxX j m)), hcb, hx, hu, hmin⟩
    -- real versions
    let a : T.Node → ℝ := fun m => (M.C m xn (r.u j m)).toReal
    let b : T.Node → ℝ := fun m => (M.V m (r.x j m)).toReal
    let c : T.Node → ℝ := fun m => (r.Vc j m (r.x j m)).toReal
    let w : T.Node → ℝ := fun m => M.Φ m / M.Φ n
    have e1 : ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m xn (r.u j m) =
        ((∑ m ∈ T.children n, w m * (a m + b m) : ℝ) : EReal) := by
      rw [coe_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      obtain ⟨h1, h2, h3, h4, -, -, hx, -, -⟩ := hfacts m hm
      unfold Model.W
      rw [← hx, EReal.coe_mul, EReal.coe_add, EReal.coe_toReal h1 h2, EReal.coe_toReal h3 h4]
    have e2 : ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
        (M.C m xn (r.u j m) + r.Vc j m (r.x j m)) =
        ((∑ m ∈ T.children n, w m * (a m + c m) : ℝ) : EReal) := by
      rw [coe_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      obtain ⟨h1, h2, -, -, h5, h6, -, -, -⟩ := hfacts m hm
      rw [EReal.coe_mul, EReal.coe_add, EReal.coe_toReal h1 h2, EReal.coe_toReal h5 h6]
    have hle1 : ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
        (M.C m xn (r.u j m) + r.Vc j m (r.x j m)) ≤ M.V n xn := by
      refine le_trans ?_ ((h31ii j n hn).2 xn)
      unfold Model.Vtilde
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (hw m)
      obtain ⟨-, -, -, -, -, -, hx, -, hmin⟩ := hfacts m hm
      apply le_iInf₂
      intro v hv
      rw [hx]
      refine (hmin v hv).trans ?_
      unfold Model.W
      exact add_le_add le_rfl (hVcV j m _ hv.2)
    rw [e2, ← EReal.coe_toReal hvt hvb, EReal.coe_le_coe_iff] at hle1
    have hgapm : ∀ m ∈ T.children n, b m - c m < ε' := by
      intro m hm
      obtain ⟨-, -, h3, h4, h5, h6, -, -, -⟩ := hfacts m hm
      have := hk m hm
      rw [ereal_fin_sub h3 h4 h5 h6, EReal.coe_lt_coe_iff] at this
      exact this
    rw [e1, ← EReal.coe_toReal hvt hvb, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have hsum : ∑ m ∈ T.children n, w m * (a m + b m) - ∑ m ∈ T.children n, w m * (a m + c m) =
        ∑ m ∈ T.children n, w m * (b m - c m) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    have hsum2 : ∑ m ∈ T.children n, w m * (b m - c m) ≤ ∑ m ∈ T.children n, w m * ε' :=
      Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hgapm m hm).le
        (div_nonneg (hΦ m).le (hΦ n).le))
    have hsum3 : ∑ m ∈ T.children n, w m * ε' = ε' := by
      rw [← Finset.sum_mul]
      simp only [w]
      rw [hwsum, one_mul]
    linarith
  rw [tendsto_order]
  constructor
  · intro a ha
    refine Eventually.of_forall fun k => lt_of_lt_of_le ha ?_
    obtain ⟨-, hVnfin, -⟩ := h31i n
    have hxn := hxX (k * τ') n
    exact (EReal.sub_nonneg (Or.inr (hVnfin _ hxn).1) (Or.inr (hVnfin _ hxn).2)).2 (hVle _)
  · intro a ha
    obtain ⟨ε', hε'0, hε'a⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have hev : ∀ᶠ k in atTop, ∀ m ∈ T.children n, M.V m (r.x (k * τ') m) -
        r.Vc (k * τ') m (r.x (k * τ') m) < ε' :=
      (eventually_all_finset _).2 (fun m hm => (tendsto_order.1 (hgap m hm)).2 _ hε'0)
    filter_upwards [hev] with k hk
    exact lt_of_le_of_lt (hDle k ε' hk) hε'a
