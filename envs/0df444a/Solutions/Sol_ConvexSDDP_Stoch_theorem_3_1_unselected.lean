-- Prove2me | solution 1 for ConvexSDDP.Stoch.theorem_3_1_unselected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:49:38.402782+00:00
-- url     : https://prove2.me/submissions/3e8365cd-e471-45ac-bc3a-853e86faf81c

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
open StochasticProg.Multistage MeasureTheory ProbabilityTheory Filter Topology

namespace SolUnsel
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

lemma x_eq_of_Vc_eq (M : Model T d p) (R : Rules T d p) (ys ys' : ℕ → T.Node → Bool)
    (r r' : RunData T d p) (hr : IsTreeRun M R ys r) (hr' : IsTreeRun M R ys' r') (j : ℕ)
    (hV : r.Vc j = r'.Vc j) : r.x j = r'.x j := by
  funext m
  suffices ∀ s, ∀ m : T.Node, (T.stage m).val = s → r.x j m = r'.x j m from this _ m rfl
  intro s
  induction s with
  | zero => intro m hm; rw [T.root_unique m hm, hr.2.2.1, hr'.2.2.1]
  | succ s ih =>
    intro m hm
    have hne : m ≠ T.root := by intro h; rw [h, T.root_stage] at hm; omega
    have ha := T.anc_stage m (by omega)
    obtain ⟨hu, -, -, hx⟩ := hr.2.2.2.1 j m hne
    obtain ⟨hu', -, -, hx'⟩ := hr'.2.2.2.1 j m hne
    have hxa : r.x j (T.anc m) = r'.x j (T.anc m) := ih _ (by omega)
    rw [hx, hx', hu, hu', hxa, hV]

lemma Vc_succ_eq (M : Model T d p) (R : Rules T d p) (ys ys' : ℕ → T.Node → Bool)
    (r r' : RunData T d p) (hr : IsTreeRun M R ys r) (hr' : IsTreeRun M R ys' r') (j : ℕ)
    (hV : r.Vc j = r'.Vc j) (hy : ys j = ys' j) : r.Vc (j + 1) = r'.Vc (j + 1) := by
  have hx := x_eq_of_Vc_eq M R ys ys' r r' hr hr' j hV
  funext n
  by_cases hn : IsLeaf T n
  · rw [hr.2.1 _ n hn, hr'.2.1 _ n hn]
  · rw [hr.2.2.2.2.2.2 j n hn, hr'.2.2.2.2.2.2 j n hn]
    have hθβ : r.θ j n = r'.θ j n ∧ r.β j n = r'.β j n := by
      obtain ⟨hsel, hns⟩ := hr.2.2.2.2.2.1 j n hn
      obtain ⟨hsel', hns'⟩ := hr'.2.2.2.2.2.1 j n hn
      cases hb : ys j n with
      | true =>
        have hb' : ys' j n = true := by rw [← hy]; exact hb
        obtain ⟨h1, h2⟩ := hsel hb
        obtain ⟨h1', h2'⟩ := hsel' hb'
        have hc : ∀ m ∈ T.children n, r.θhat j m = r'.θhat j m ∧ r.βhat j m = r'.βhat j m := by
          intro m hm
          have hanc := (stage_child hm).2
          have hne := ne_root_of_child hm
          obtain ⟨a1, a2, -, -⟩ := hr.2.2.2.2.1 j m hne (by rw [hanc]; exact hb)
          obtain ⟨a1', a2', -, -⟩ := hr'.2.2.2.2.1 j m hne (by rw [hanc]; exact hb')
          obtain ⟨u1, -, -, x1⟩ := hr.2.2.2.1 j m hne
          obtain ⟨u1', -, -, x1'⟩ := hr'.2.2.2.1 j m hne
          rw [a1, a1', a2, a2', u1, u1', hx, hV]
          exact ⟨rfl, rfl⟩
        rw [h1, h1', h2, h2']
        constructor
        · exact Finset.sum_congr rfl (fun m hm => by rw [(hc m hm).1])
        · exact Finset.sum_congr rfl (fun m hm => by rw [(hc m hm).2])
      | false =>
        have hb' : ys' j n = false := by rw [← hy]; exact hb
        obtain ⟨h1, h2, -⟩ := hns hb
        obtain ⟨h1', h2', -⟩ := hns' hb'
        rw [h1, h1', h2, h2', hx, hV]
        exact ⟨rfl, rfl⟩
    rw [hθβ.1, hθβ.2, hx, hV]

lemma Vc_eq_of_agree (M : Model T d p) (R : Rules T d p) (ys ys' : ℕ → T.Node → Bool)
    (r r' : RunData T d p) (hr : IsTreeRun M R ys r) (hr' : IsTreeRun M R ys' r') (N : ℕ)
    (hag : ∀ j < N, ys j = ys' j) : ∀ j ≤ N, r.Vc j = r'.Vc j := by
  intro j hj
  induction j with
  | zero =>
    funext n
    by_cases hn : IsLeaf T n
    · rw [hr.2.1 0 n hn, hr'.2.1 0 n hn]
    · rw [hr.1 n hn, hr'.1 n hn]
  | succ j ih =>
    exact Vc_succ_eq M R ys ys' r r' hr hr' j (ih (by omega)) (hag j (by omega))

lemma measurableSet_of_depends {Ω : Type*} [MeasurableSpace Ω] {N' : Type*} [Finite N']
    (Y : ℕ → Ω → N' → Bool) (N : ℕ) (S : Set Ω)
    (hS : ∀ ω ω', (∀ j < N, Y j ω = Y j ω') → ω ∈ S → ω' ∈ S) :
    MeasurableSet[⨆ j, ⨆ (_ : j < N), MeasurableSpace.comap (Y j) inferInstance] S := by
  let Φ : Ω → (Fin N → N' → Bool) := fun ω i => Y i ω
  have hΦ : Measurable[⨆ j, ⨆ (_ : j < N), MeasurableSpace.comap (Y j) inferInstance] Φ := by
    refine @measurable_pi_lambda Ω (Fin N) (fun _ => N' → Bool)
      (⨆ j, ⨆ (_ : j < N), MeasurableSpace.comap (Y j) inferInstance) _ Φ (fun i => ?_)
    exact (comap_measurable (Y i)).mono
      (le_iSup₂_of_le (f := fun j (_ : j < N) => MeasurableSpace.comap (Y j) inferInstance)
        (i : ℕ) i.2 le_rfl) le_rfl
  have hSeq : S = Φ ⁻¹' (Φ '' S) := by
    ext ω
    constructor
    · intro h; exact ⟨ω, h, rfl⟩
    · rintro ⟨ω', h', he⟩
      exact hS ω' ω (fun j hj => congrFun he ⟨j, hj⟩) h'
  rw [hSeq]
  exact hΦ (Set.toFinite _).measurableSet


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

/-- Probabilistic part: Lévy's conditional Borel–Cantelli lemma. -/
lemma levy_step {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hGmono : Monotone G) (hGle : ∀ k, G k ≤ m0)
    (A B : ℕ → Set Ω) (hA : ∀ k, MeasurableSet[G k] (A k))
    (hA1 : ∀ k, MeasurableSet[G k] (A (k + 1)))
    (hB : ∀ k, MeasurableSet[G k] (B k))
    (mB : ℕ → MeasurableSpace Ω) (hmB : ∀ k, mB k ≤ m0) (hBm : ∀ k, MeasurableSet[mB k] (B k))
    (hind : ∀ k, Indep (mB (k + 1)) (G k) P) (hp : ∀ k, P (B k) = P (B 0))
    (hp0 : 0 < P (B 0)) :
    ∀ᵐ ω ∂P, {k | ω ∈ A k ∧ ω ∈ B k}.Finite → {k | ω ∈ A k}.Finite := by
  let ℱ : Filtration ℕ m0 := ⟨G, hGmono, hGle⟩
  have hs : ∀ k, MeasurableSet[ℱ k] (A k ∩ B k) := fun k => (hA k).inter (hB k)
  have levy := ae_mem_limsup_atTop_iff (ℱ := ℱ) P hs
  set q := P.real (B 0) with hqdef
  have hq : 0 < q := by
    rw [hqdef, Measure.real]
    exact ENNReal.toReal_pos hp0.ne' (measure_ne_top _ _)
  have hce : ∀ k, P[(A (k + 1) ∩ B (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] =ᵐ[P]
      (A (k + 1)).indicator (fun _ => q) := by
    intro k
    rw [Set.inter_indicator_one]
    have hmeasB : MeasurableSet (B (k + 1)) := hmB _ _ (hBm (k + 1))
    have h1 := condExp_stronglyMeasurable_mul_of_bound (μ := P) (m := ℱ k) (hGle k)
      (f := (A (k + 1)).indicator 1) (g := (B (k + 1)).indicator 1)
      (stronglyMeasurable_one.indicator (hA1 k)) ((integrable_const (1 : ℝ)).indicator hmeasB) 1
      (Eventually.of_forall fun ω => by
        by_cases h : ω ∈ A (k + 1) <;> simp [h])
    have h2 := condExp_indep_eq (μ := P) (hmB (k + 1)) (hGle k)
      (f := (B (k + 1)).indicator (1 : Ω → ℝ))
      (stronglyMeasurable_one.indicator (hBm (k + 1))) (hind k)
    rw [integral_indicator_one hmeasB] at h2
    have hq' : P.real (B (k + 1)) = q := by rw [hqdef, Measure.real, Measure.real, hp]
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, Pi.mul_apply, e2, hq']
    by_cases h : ω ∈ A (k + 1) <;> simp [h]
  have hce' := ae_all_iff.2 hce
  filter_upwards [levy, hce'] with ω hl hc
  intro hfin
  by_contra hinfA
  have hinfA' : {k | ω ∈ A k}.Infinite := hinfA
  set u : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, (A (k + 1)).indicator (fun _ => q) ω with hu
  have hu_mono : Monotone u := by
    refine monotone_nat_of_le_succ (fun N => ?_)
    simp only [hu, Finset.sum_range_succ]
    have : 0 ≤ (A (N + 1)).indicator (fun _ => q) ω :=
      Set.indicator_nonneg (fun _ _ => hq.le) _
    linarith
  have hgrow : ∀ M : ℕ, ∃ N, (M : ℝ) * q ≤ u N := by
    intro M
    induction M with
    | zero => exact ⟨0, by simp [hu]⟩
    | succ M ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨k', hk'mem, hk'gt⟩ := hinfA'.exists_gt N
      obtain ⟨k, rfl⟩ : ∃ k, k' = k + 1 := ⟨k' - 1, by omega⟩
      refine ⟨k + 1, ?_⟩
      have e1 : u (k + 1) = u k + q := by
        simp only [hu, Finset.sum_range_succ]
        rw [Set.indicator_of_mem (show ω ∈ A (k + 1) from hk'mem)]
      have e2 : u N ≤ u k := hu_mono (by omega)
      push_cast
      linarith
  have hsum : Tendsto (fun N => ∑ k ∈ Finset.range N,
      P[(A (k + 1) ∩ B (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω) atTop atTop := by
    simp_rw [hc]
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨M, hM⟩ := exists_nat_ge (b / q)
    obtain ⟨N, hN⟩ := hgrow M
    refine ⟨N, fun a ha => ?_⟩
    have h1 := hu_mono ha
    have h2 : b ≤ M * q := by rwa [div_le_iff₀ hq] at hM
    show b ≤ u a
    linarith
  have hmem := hl.2 hsum
  rw [mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite] at hmem
  exact hmem hfin

end SolUnsel

open ConvexSDDP.Stoch SolUnsel in
theorem solution {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → T.Node → Bool) (hY : ∀ k, Measurable (Y k)) (τ : ℕ)
    (hadm : IsAdmissible T P Y τ) (r : Ω → RunData T d p)
    (hr : ∀ ω, IsTreeRun M R (fun k => Y k ω) (r ω))
    (n : T.Node) (hn : ¬ IsLeaf T n)
    (h32 : ∀ᵐ ω ∂P, Tendsto
      (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
      (atTop ⊓ 𝓟 {k | ytilde Y τ k n ω = true}) (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
      atTop (𝓝 0) := by
  classical
  have hτ : 0 < τ := hadm.1
  have hxX : ∀ ω k, (r ω).x k n ∈ M.X n := by
    intro ω k
    by_cases hroot : n = T.root
    · rw [hroot, (hr ω).2.2.1 k]
      exact hH2.2.1
    · obtain ⟨-, hu, -, hx⟩ := (hr ω).2.2.2.1 k n hroot
      rw [hx]
      exact hu.2
  obtain ⟨-, hVfin, L, hL⟩ := lemma_3_1_i M hH2 n
  have hcompact : IsCompact (M.X n) := (hH2.2.2.1 n).2
  have hmono : ∀ ω i j, i ≤ j → ∀ y, (r ω).Vc i n y ≤ (r ω).Vc j n y := by
    intro ω i j hij y
    induction hij with
    | refl => exact le_rfl
    | step _ ih =>
      refine ih.trans ?_
      rw [(hr ω).2.2.2.2.2.2 _ n hn]
      exact le_max_left _ _
  have hle : ∀ ω j, ∀ y ∈ M.X n, (r ω).Vc j n y ≤ M.V n y := by
    intro ω j y hy
    have h := lemma_3_1_ii M hH2 R (fun k => Y k ω) (r ω) (hr ω) j n hn
    exact (h.1 y (subset_affineSpan ℝ _ hy)).trans (h.2 y)
  -- Step 1 (pathwise)
  have step1' : ∀ ω, Tendsto
      (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
      (atTop ⊓ 𝓟 {k | ytilde Y τ k n ω = true}) (𝓝 0) → ∀ ε : ℝ, 0 < ε →
      {k | (ε : EReal) ≤ M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ) n ((r ω).x (k * τ) n) ∧
        k ∈ {k | ytilde Y τ k n ω = true}}.Finite := by
    intro ω hω ε hε
    obtain ⟨α, -, -, hα⟩ := lemma_3_1_iii M hH2 R (fun k => Y k ω) (r ω) (hr ω) n hn
    exact step1 (M.X n) hcompact (fun k => (r ω).x (k * τ) n) (fun k => hxX ω _) (M.V n)
      (fun k => (r ω).Vc k n) hVfin L hL α hα (hmono ω) (hle ω) τ hτ _ hω ε hε
  -- determinism of the run
  have hdet : ∀ ω ω' N, (∀ j < N, Y j ω = Y j ω') → ∀ K ≤ N,
      (r ω).Vc K = (r ω').Vc K ∧ (r ω).x K = (r ω').x K := by
    intro ω ω' N hag K hK
    have hV := Vc_eq_of_agree M R _ _ _ _ (hr ω) (hr ω') N hag K hK
    exact ⟨hV, x_eq_of_Vc_eq M R _ _ _ _ (hr ω) (hr ω') K hV⟩
  have hdepB : ∀ k ω ω', (∀ j < (k + 1) * τ, Y j ω = Y j ω') →
      ytilde Y τ k n ω = ytilde Y τ k n ω' := by
    intro k ω ω' hag
    have : ∀ κ < τ, Y (k * τ + κ) ω = Y (k * τ + κ) ω' := fun κ hκ =>
      hag _ (by nlinarith)
    simp only [ytilde]
    congr 1
    apply propext
    constructor
    · rintro ⟨κ, hκ, h⟩; exact ⟨κ, hκ, by rw [← this κ hκ]; exact h⟩
    · rintro ⟨κ, hκ, h⟩; exact ⟨κ, hκ, by rw [this κ hκ]; exact h⟩
  -- Step 2 (probabilistic)
  have step2 : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P,
      {k | ω ∈ {ω | (ε : EReal) ≤ M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ) n ((r ω).x (k * τ) n)} ∧
        ω ∈ {ω | ytilde Y τ k n ω = true}}.Finite →
      {k | ω ∈ {ω | (ε : EReal) ≤ M.V n ((r ω).x (k * τ) n) -
        (r ω).Vc (k * τ) n ((r ω).x (k * τ) n)}}.Finite := by
    intro ε hε
    have hGmono : Monotone (fun k : ℕ => ⨆ j, ⨆ (_ : j < (k + 1) * τ),
        MeasurableSpace.comap (Y j) (inferInstance : MeasurableSpace (T.Node → Bool))) := by
      intro a b hab
      refine iSup_mono fun j => iSup_mono' fun hj => ⟨lt_of_lt_of_le hj ?_, le_rfl⟩
      exact Nat.mul_le_mul_right τ (by omega)
    have hGle : ∀ k, (⨆ j, ⨆ (_ : j < (k + 1) * τ),
        MeasurableSpace.comap (Y j) (inferInstance : MeasurableSpace (T.Node → Bool))) ≤
        (inferInstance : MeasurableSpace Ω) :=
      fun k => iSup₂_le fun j _ => (hY j).comap_le
    have hBset : ∀ k (S : Set Bool), MeasurableSet[⨆ j, ⨆ (_ : j < (k + 1) * τ),
        MeasurableSpace.comap (Y j) (inferInstance : MeasurableSpace (T.Node → Bool))]
        ((fun ω => ytilde Y τ k n ω) ⁻¹' S) := by
      intro k S
      refine measurableSet_of_depends Y ((k + 1) * τ) _ (fun ω ω' hag hmem => ?_)
      simp only [Set.mem_preimage] at hmem ⊢
      rw [← hdepB k ω ω' hag]
      exact hmem
    refine levy_step P _ hGmono hGle
      (fun k => {ω | (ε : EReal) ≤ M.V n ((r ω).x (k * τ) n) -
        (r ω).Vc (k * τ) n ((r ω).x (k * τ) n)})
      (fun k => {ω | ytilde Y τ k n ω = true}) ?_ ?_ ?_
      (fun k => MeasurableSpace.comap (fun ω => ytilde Y τ k n ω) inferInstance) ?_ ?_ ?_ ?_ ?_
    · intro k
      refine measurableSet_of_depends Y ((k + 1) * τ) _ (fun ω ω' hag hmem => ?_)
      obtain ⟨h1, h2⟩ := hdet ω ω' _ hag (k * τ) (Nat.mul_le_mul_right τ (by omega))
      simp only [Set.mem_ofPred_eq] at hmem ⊢
      rw [← h1, ← h2]
      exact hmem
    · intro k
      refine measurableSet_of_depends Y ((k + 1) * τ) _ (fun ω ω' hag hmem => ?_)
      obtain ⟨h1, h2⟩ := hdet ω ω' _ hag ((k + 1) * τ) le_rfl
      simp only [Set.mem_ofPred_eq] at hmem ⊢
      rw [← h1, ← h2]
      exact hmem
    · intro k
      exact hBset k {true}
    · intro k
      refine Measurable.comap_le ?_
      intro S _
      exact hGle k _ (hBset k S)
    · intro k
      exact ⟨{true}, measurableSet_singleton _, rfl⟩
    · intro k
      exact (hadm.2.2.1 n hn).2 (k + 1)
    · intro k
      exact ((hadm.2.2.1 n hn).1.2 k).measure_mem_eq (measurableSet_singleton true)
    · exact hadm.2.2.2 n hn 0
  -- Step 3
  have hall := ae_all_iff.2 (fun j : ℕ => step2 (1 / ((j : ℝ) + 1)) (by positivity))
  filter_upwards [h32, hall] with ω hω hfin
  have hF : ∀ j : ℕ, {k | ((1 / ((j : ℝ) + 1) : ℝ) : EReal) ≤
      M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ) n ((r ω).x (k * τ) n)}.Finite :=
    fun j => hfin j (step1' ω hω _ (by positivity))
  have hnonneg : ∀ k, 0 ≤ M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n) :=
    fun k => (EReal.sub_nonneg (Or.inl (hVfin _ (hxX ω _)).1) (Or.inl (hVfin _ (hxX ω _)).2)).2
      (hle ω _ _ (hxX ω _))
  have hgh : ∀ k, M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n) ≤
      M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ) n ((r ω).x (k * τ) n) :=
    fun k => EReal.sub_le_sub le_rfl (hmono ω _ _ (Nat.le_succ _) _)
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Eventually.of_forall fun k => lt_of_lt_of_le ha (hnonneg k)
  · intro a ha
    obtain ⟨ε', hε'0, hε'a⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    have hε'0' : (0 : ℝ) < ε' := by exact_mod_cast hε'0
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε'0'
    have hev := (hF j).eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at hev
    filter_upwards [hev] with k hk
    simp only [not_le] at hk
    calc _ ≤ _ := hgh k
      _ < _ := hk
      _ < (ε' : EReal) := by exact_mod_cast hj
      _ < a := hε'a
