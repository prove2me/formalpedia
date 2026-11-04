-- Prove2me | solution 1 for ConvexSDDP.Stoch.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:00:45.049758+00:00
-- url     : https://prove2.me/submissions/a6c580bc-621f-4e75-b3de-22b07713557a

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Definitions.Def_ConvexSDDP_Stoch_Selection
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_i
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_ii
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_1_iii
import Theorems.Thm_ConvexSDDP_Stoch_lemma_3_2
import Theorems.Thm_ConvexSDDP_Stoch_lemma_5_3
import Theorems.Thm_ConvexSDDP_Stoch_eq_26
open StochasticProg.Multistage MeasureTheory ProbabilityTheory Filter Topology
open scoped Pointwise

namespace SolE32
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
lemma step1g {E : Type*} [NormedAddCommGroup E] (K : Set E) (hK : IsCompact K) (x : ℕ → E)
    (hx : ∀ k, x k ∈ K) (f : E → EReal) (F : ℕ → E → EReal)
    (hf : ∀ y ∈ K, f y ≠ ⊤ ∧ f y ≠ ⊥) (L : ℝ)
    (hL : ∀ y ∈ K, ∀ z ∈ K, |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖)
    (α : ℝ) (hα : ∀ k y z, F k y ≠ ⊥ → F k z ≠ ⊥ ∧ |(F k y).toReal - (F k z).toReal| ≤ α * ‖y - z‖)
    (hmono : ∀ i j, i ≤ j → ∀ y, F i y ≤ F j y) (hle : ∀ k, ∀ y ∈ K, F k y ≤ f y)
    (ia ib : ℕ → ℕ) (S : Set ℕ) (hab : ∀ k1 k2, k1 < k2 → k1 ∈ S → k2 ∈ S → ia k1 ≤ ib k2)
    (hg : Tendsto (fun k => f (x k) - F (ia k) (x k)) (atTop ⊓ 𝓟 S) (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    {k | (ε : EReal) ≤ f (x k) - F (ib k) (x k) ∧ k ∈ S}.Finite := by
  by_contra hinf
  let pr : ℕ → Prop := fun k => (ε : EReal) ≤ f (x k) - F (ib k) (x k) ∧ k ∈ S
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
  have h2 : ∀ᶠ i in atTop, f (x (Nat.nth pr (ψ i))) - F (ia (Nat.nth pr (ψ i)))
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
  have hb1 : F (ia k1) x1 ≠ ⊥ := by
    intro hb
    rw [hb, EReal.sub_bot hf1b] at hg1
    exact absurd hg1 (not_lt.2 le_top)
  obtain ⟨hb2, hlip⟩ := hα (ia k1) x1 x2 hb1
  have hkk : ia k1 ≤ ib k2 := hab k1 k2 hk (hφI (ψ N)).2 (hφI (ψ (N + 1))).2
  have hmon : F (ia k1) x2 ≤ F (ib k2) x2 := hmono _ _ hkk x2
  have hc2b : F (ib k2) x2 ≠ ⊥ := fun h => hb2 (le_bot_iff.1 (h ▸ hmon))
  have hc2t : F (ib k2) x2 ≠ ⊤ := ne_top_of_le_ne_top hf2t (hle _ x2 hx2)
  have hb1t : F (ia k1) x1 ≠ ⊤ := ne_top_of_le_ne_top hf1t (hle _ x1 hx1)
  have hb2t : F (ia k1) x2 ≠ ⊤ := ne_top_of_le_ne_top hf2t (hle _ x2 hx2)
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

end SolE32

open ConvexSDDP.Stoch SolE32 in
theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → T.Node → Bool) (hY : ∀ k, Measurable (Y k)) (τ : ℕ)
    (hadm : IsAdmissible T P Y τ) (r : Ω → RunData T d p)
    (hr : ∀ ω, IsTreeRun M R (fun k => Y k ω) (r ω))
    (n : T.Node) (hn : ¬ IsLeaf T n)
    (hind : ∀ᵐ ω ∂P, ∀ m ∈ T.children n,
      Tendsto (fun k => M.V m ((r ω).x (k * τ) m) - (r ω).Vc (k * τ + 1) m ((r ω).x (k * τ) m))
        atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
      (atTop ⊓ 𝓟 {k | ytilde Y τ k n ω = true}) (𝓝 0) := by
  classical
  have hτ : 0 < τ := hadm.1
  filter_upwards [hind] with ω hω
  set ys : ℕ → T.Node → Bool := fun k => Y k ω with hys
  set rr := r ω
  have hrr : IsTreeRun M R ys rr := hr ω
  have hΦ : ∀ m, 0 < M.Φ m := hH2.1.1
  have hw : ∀ m : T.Node, (0 : EReal) ≤ ((M.Φ m / M.Φ n : ℝ) : EReal) := fun m =>
    EReal.coe_nonneg.mpr (div_nonneg (hΦ m).le (hΦ n).le)
  have hwsum : ∑ m ∈ T.children n, (M.Φ m / M.Φ n) = 1 := by
    rw [← Finset.sum_div, hH2.1.2.2 n hn, div_self (hΦ n).ne']
  have hxX : ∀ k m, rr.x k m ∈ M.X m := by
    intro k m
    by_cases hroot : m = T.root
    · rw [hroot, hrr.2.2.1 k]
      exact hH2.2.1
    · obtain ⟨-, hu, -, hx⟩ := hrr.2.2.2.1 k m hroot
      rw [hx]
      exact hu.2
  have h31i := lemma_3_1_i M hH2
  have h31ii := lemma_3_1_ii M hH2 R ys rr hrr
  have hVcV : ∀ k m, ∀ z ∈ M.X m, rr.Vc k m z ≤ M.V m z := by
    intro k m z hz
    by_cases hm : IsLeaf T m
    · rw [hrr.2.1 k m hm]
    · exact ((h31ii k m hm).1 z (subset_affineSpan ℝ _ hz)).trans ((h31ii k m hm).2 z)
  have hmonoAll : ∀ m i j, i ≤ j → ∀ y, rr.Vc i m y ≤ rr.Vc j m y := by
    intro m i j hij y
    induction hij with
    | refl => exact le_rfl
    | step _ ih =>
      refine ih.trans ?_
      by_cases hml : IsLeaf T m
      · rw [hrr.2.1 _ m hml, hrr.2.1 _ m hml]
      · rw [hrr.2.2.2.2.2.2 _ m hml]
        exact le_max_left _ _
  -- η → 0 (Lemma 3.2)
  have hη := lemma_3_2 M hH2 R ys rr hrr n hn τ hτ hω
  -- Lemma 5.2 at the children
  have hgap : ∀ m ∈ T.children n, Tendsto (fun k => M.V m (rr.x (k * τ) m) -
      rr.Vc (k * τ) m (rr.x (k * τ) m)) atTop (𝓝 0) := by
    intro m hm
    obtain ⟨-, hVfin, L, hL⟩ := h31i m
    by_cases hml : IsLeaf T m
    · have : ∀ k, M.V m (rr.x (k * τ) m) - rr.Vc (k * τ) m (rr.x (k * τ) m) = 0 := fun k => by
        rw [hrr.2.1 _ m hml]
        exact EReal.sub_self (hVfin _ (hxX _ _)).1 (hVfin _ (hxX _ _)).2
      simp only [this]
      exact tendsto_const_nhds
    · obtain ⟨α, -, -, hα⟩ := lemma_3_1_iii M hH2 R ys rr hrr m hml
      apply tendsto_of_finite
      · intro k
        exact (EReal.sub_nonneg (Or.inl (hVfin _ (hxX _ _)).1) (Or.inl (hVfin _ (hxX _ _)).2)).2
          (hVcV _ m _ (hxX _ _))
      · intro ε hε
        have h1 := step1g (M.X m) (hH2.2.2.1 m).2 (fun k => rr.x (k * τ) m) (fun k => hxX _ _)
          (M.V m) (fun k => rr.Vc k m) hVfin L hL α hα (hmonoAll m) (fun k => hVcV k m)
          (fun k => k * τ + 1) (fun k => k * τ) Set.univ
          (fun k1 k2 hk _ _ => by
            have : (k1 + 1) * τ ≤ k2 * τ := Nat.mul_le_mul_right τ hk
            show k1 * τ + 1 ≤ k2 * τ; nlinarith)
          (by rw [principal_univ, inf_top_eq]; exact hω m hm) ε hε
        exact h1.subset (fun k hk => ⟨hk, Set.mem_univ _⟩)
  -- the selected index inside the block
  let S : Set ℕ := {k | ytilde Y τ k n ω = true}
  have hSdef : ∀ k, k ∈ S ↔ ∃ κ < τ, ys (k * τ + κ) n = true := by
    intro k
    show ytilde Y τ k n ω = true ↔ _
    simp [ytilde, hys]
  let κf : ℕ → ℕ := fun k => if h : ∃ κ < τ, ys (k * τ + κ) n = true then Classical.choose h else 0
  have hκf : ∀ k ∈ S, κf k < τ ∧ ys (k * τ + κf k) n = true := by
    intro k hk
    have h := (hSdef k).1 hk
    simp only [κf, dif_pos h]
    exact Classical.choose_spec h
  -- (31): exactness w.r.t. V^{kτ+κ_k}
  have hlowcut : ∀ k ∈ S, ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
      (M.C m (rr.x (k * τ) n) (rr.u (k * τ) m) + rr.Vc (k * τ) m (rr.x (k * τ) m)) ≤
      rr.Vc (k * τ + κf k + 1) n (rr.x (k * τ) n) := by
    intro k hk
    obtain ⟨hκ, hsel⟩ := hκf k hk
    set i := k * τ + κf k
    have h53 := (lemma_5_3 M R ys rr hrr τ hτ (hadm.2.1 ω) k (κf k) n hκ hn hsel).1
    have h26 := eq_26 M hH2 R ys rr hrr i n hn
    rw [← h53, h26.1, h26.2 hsel, h53]
    apply Finset.sum_le_sum
    intro m hm
    apply mul_le_mul_of_nonneg_left _ (hw m)
    have hne := ne_root_of_child hm
    have hanc := (stage_child hm).2
    obtain ⟨-, hu0, hmin0, hx0⟩ := hrr.2.2.2.1 (k * τ) m hne
    obtain ⟨-, hui, -, hxi⟩ := hrr.2.2.2.1 i m hne
    rw [hanc] at hu0 hmin0 hx0 hui hxi
    rw [h53] at hui hxi
    rw [hx0, hxi]
    refine (hmin0 _ hui).trans ?_
    exact add_le_add le_rfl (hmonoAll m _ _ (by omega) _)
  have h31 : Tendsto (fun k => M.V n (rr.x (k * τ) n) - rr.Vc (k * τ + κf k + 1) n (rr.x (k * τ) n))
      (atTop ⊓ 𝓟 S) (𝓝 0) := by
    obtain ⟨-, hVnfin, -⟩ := h31i n
    rw [tendsto_order]
    constructor
    · intro a ha
      refine Eventually.of_forall fun k => lt_of_lt_of_le ha ?_
      have hxn := hxX (k * τ) n
      exact (EReal.sub_nonneg (Or.inl (hVnfin _ hxn).1) (Or.inl (hVnfin _ hxn).2)).2
        (hVcV _ n _ hxn)
    · intro a ha
      obtain ⟨ε', hε'0, hε'a⟩ := EReal.lt_iff_exists_real_btwn.1 ha
      have hε'0' : (0 : ℝ) < ε' := by exact_mod_cast hε'0
      have hev1 : ∀ᶠ k in atTop, ∀ m ∈ T.children n, M.V m (rr.x (k * τ) m) -
          rr.Vc (k * τ) m (rr.x (k * τ) m) < ((ε' / 2 : ℝ) : EReal) :=
        (eventually_all_finset _).2 (fun m hm => (tendsto_order.1 (hgap m hm)).2 _
          (by exact_mod_cast (by positivity : (0 : ℝ) < ε' / 2)))
      have hev2 := (tendsto_order.1 hη).1 ((-(ε' / 2) : ℝ) : EReal)
        (by exact_mod_cast (by linarith : -(ε' / 2) < (0 : ℝ)))
      have hev3 := (tendsto_order.1 hη).2 ((ε' / 2 : ℝ) : EReal)
        (by exact_mod_cast (by positivity : (0 : ℝ) < ε' / 2))
      rw [eventually_inf_principal]
      filter_upwards [hev1, hev2, hev3] with k hk1 hk2 hk3 hkS
      refine lt_of_le_of_lt ?_ hε'a
      -- real arithmetic
      set xn := rr.x (k * τ) n
      have hxn : xn ∈ M.X n := hxX _ n
      obtain ⟨hvt, hvb⟩ := hVnfin xn hxn
      have hδ := hH2.2.2.2.2.2.2.2
      have hxnb : xn ∈ M.X n + Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M.δ := by
        have := Set.add_mem_add hxn
          (Metric.mem_ball_self (x := (0 : EuclideanSpace ℝ (Fin d))) hδ.1)
        rwa [add_zero] at this
      have hfacts : ∀ m ∈ T.children n,
          M.C m xn (rr.u (k * τ) m) ≠ ⊤ ∧ M.C m xn (rr.u (k * τ) m) ≠ ⊥ ∧
          M.V m (rr.x (k * τ) m) ≠ ⊤ ∧ M.V m (rr.x (k * τ) m) ≠ ⊥ ∧
          rr.Vc (k * τ) m (rr.x (k * τ) m) ≠ ⊤ ∧ rr.Vc (k * τ) m (rr.x (k * τ) m) ≠ ⊥ ∧
          rr.x (k * τ) m = M.f m (xn, rr.u (k * τ) m) := by
        intro m hm
        have hne := ne_root_of_child hm
        have hanc := (stage_child hm).2
        obtain ⟨-, hu, -, hx⟩ := hrr.2.2.2.1 (k * τ) m hne
        rw [hanc] at hu hx
        obtain ⟨hbt, hbb⟩ := (h31i m).2.1 _ (hxX _ m)
        have hcb : rr.Vc (k * τ) m (rr.x (k * τ) m) ≠ ⊥ := by
          intro h
          have := hk1 m hm
          rw [h, EReal.sub_bot hbb] at this
          exact absurd this (not_lt.2 le_top)
        exact ⟨((hδ.2 n hn xn hxnb m hm).2 _ hu.1).ne, (hH2.2.2.2.2.1 m hne).1.1 (xn, rr.u (k * τ) m),
          hbt, hbb, ne_top_of_le_ne_top hbt (hVcV _ m _ (hxX _ m)), hcb, hx⟩
      let a : T.Node → ℝ := fun m => (M.C m xn (rr.u (k * τ) m)).toReal
      let b : T.Node → ℝ := fun m => (M.V m (rr.x (k * τ) m)).toReal
      let c : T.Node → ℝ := fun m => (rr.Vc (k * τ) m (rr.x (k * τ) m)).toReal
      let w : T.Node → ℝ := fun m => M.Φ m / M.Φ n
      have e1 : ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m xn (rr.u (k * τ) m) =
          ((∑ m ∈ T.children n, w m * (a m + b m) : ℝ) : EReal) := by
        rw [coe_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        obtain ⟨h1, h2, h3, h4, -, -, hx⟩ := hfacts m hm
        unfold Model.W
        rw [← hx, EReal.coe_mul, EReal.coe_add, EReal.coe_toReal h1 h2, EReal.coe_toReal h3 h4]
      have e2 : ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
          (M.C m xn (rr.u (k * τ) m) + rr.Vc (k * τ) m (rr.x (k * τ) m)) =
          ((∑ m ∈ T.children n, w m * (a m + c m) : ℝ) : EReal) := by
        rw [coe_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        obtain ⟨h1, h2, -, -, h5, h6, -⟩ := hfacts m hm
        rw [EReal.coe_mul, EReal.coe_add, EReal.coe_toReal h1 h2, EReal.coe_toReal h5 h6]
      have hgapm : ∀ m ∈ T.children n, b m - c m < ε' / 2 := by
        intro m hm
        obtain ⟨-, -, h3, h4, h5, h6, -⟩ := hfacts m hm
        have := hk1 m hm
        rw [ereal_fin_sub h3 h4 h5 h6, EReal.coe_lt_coe_iff] at this
        exact this
      have hlow := hlowcut k hkS
      rw [e2] at hlow
      set vc := rr.Vc (k * τ + κf k + 1) n xn
      have hvct : vc ≠ ⊤ := ne_top_of_le_ne_top hvt (hVcV _ n _ hxn)
      have hvcb : vc ≠ ⊥ := fun h => by
        rw [h] at hlow
        exact absurd hlow (not_le.2 (EReal.bot_lt_coe _))
      rw [← EReal.coe_toReal hvct hvcb, EReal.coe_le_coe_iff] at hlow
      rw [e1, ← EReal.coe_toReal hvt hvb, ← EReal.coe_sub] at hk2
      rw [EReal.coe_lt_coe_iff] at hk2
      rw [ereal_fin_sub hvt hvb hvct hvcb, EReal.coe_le_coe_iff]
      have hsum : ∑ m ∈ T.children n, w m * (a m + b m) - ∑ m ∈ T.children n, w m * (a m + c m) =
          ∑ m ∈ T.children n, w m * (b m - c m) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun m _ => by ring)
      have hsum2 : ∑ m ∈ T.children n, w m * (b m - c m) ≤ ∑ m ∈ T.children n, w m * (ε' / 2) :=
        Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hgapm m hm).le
          (div_nonneg (hΦ m).le (hΦ n).le))
      have hsum3 : ∑ m ∈ T.children n, w m * (ε' / 2) = ε' / 2 := by
        rw [← Finset.sum_mul]
        simp only [w]
        rw [hwsum, one_mul]
      linarith
  -- (32) by the subsequence version of Lemma 5.2
  obtain ⟨-, hVnfin, L, hL⟩ := h31i n
  obtain ⟨α, -, -, hα⟩ := lemma_3_1_iii M hH2 R ys rr hrr n hn
  have hfinS : ∀ ε : ℝ, 0 < ε → {k | (ε : EReal) ≤ M.V n (rr.x (k * τ) n) -
      rr.Vc (k * τ + 1) n (rr.x (k * τ) n) ∧ k ∈ S}.Finite := by
    intro ε hε
    exact step1g (M.X n) (hH2.2.2.1 n).2 (fun k => rr.x (k * τ) n) (fun k => hxX _ _)
      (M.V n) (fun k => rr.Vc k n) hVnfin L hL α hα (hmonoAll n) (fun k => hVcV k n)
      (fun k => k * τ + κf k + 1) (fun k => k * τ + 1) S
      (fun k1 k2 hk hk1 _ => by
        have h1 := (hκf k1 hk1).1
        have : (k1 + 1) * τ ≤ k2 * τ := Nat.mul_le_mul_right τ hk
        show k1 * τ + κf k1 + 1 ≤ k2 * τ + 1; nlinarith)
      h31 ε hε
  rw [tendsto_order]
  constructor
  · intro a ha
    refine Eventually.of_forall fun k => lt_of_lt_of_le ha ?_
    have hxn := hxX (k * τ) n
    exact (EReal.sub_nonneg (Or.inl (hVnfin _ hxn).1) (Or.inl (hVnfin _ hxn).2)).2
      (hVcV _ n _ hxn)
  · intro a ha
    obtain ⟨ε', hε'0, hε'a⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have hε'0' : (0 : ℝ) < ε' := by exact_mod_cast hε'0
    have hev := (hfinS ε' hε'0').eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at hev
    rw [eventually_inf_principal]
    filter_upwards [hev] with k hk hkS
    have : ¬ ((ε' : EReal) ≤ M.V n (rr.x (k * τ) n) - rr.Vc (k * τ + 1) n (rr.x (k * τ) n)) :=
      fun h => hk ⟨h, hkS⟩
    exact (not_le.1 this).trans hε'a
