-- Prove2me | solution 1 for BauerleRiederMDP.FiniteHorizon.theorem_2_2_3
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T21:22:53.031802+00:00
-- url     : https://prove2.me/submissions/6b81e1c9-054e-40c9-b592-dd79b2fd4b1f

import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Representation
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Vpi
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_V
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_histRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_VHist

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel Hist HistPolicy histState measurable_histState
  erealIntegral IsDecisionRule)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

namespace Thm223Sol

open BauerleRiederMDP.FiniteHorizon

variable {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-! ### Basic facts about `pathReward` and `pathKernel` -/

lemma pathReward_split (r : ℕ → E × A → ℝ) (g : E → ℝ) (n₀ j₀ k : ℕ) (h : Hist E A (j₀ + k)) :
    pathReward r g n₀ j₀ k h = pathReward r (fun _ => 0) n₀ j₀ k h + g (histState (j₀ + k) h) := by
  cases k with
  | zero => simp [pathReward]
  | succ k =>
    obtain ⟨h1, a, x⟩ := h
    simp [pathReward, histState]

lemma pathReward_nonneg (r : ℕ → E × A → ℝ) (hr : ∀ i xa, 0 ≤ r i xa) (n₀ j₀ k : ℕ)
    (h : Hist E A (j₀ + k)) : 0 ≤ pathReward r (fun _ => 0) n₀ j₀ k h := by
  induction k with
  | zero => simp [pathReward]
  | succ k ih =>
    obtain ⟨h1, a, x⟩ := h
    simp only [pathReward]
    have := ih h1
    have := hr (n₀ + k) (histState (j₀ + k) h1, a)
    linarith

lemma pathReward_nonneg' (r : ℕ → E × A → ℝ) (g : E → ℝ) (hr : ∀ i xa, 0 ≤ r i xa)
    (hg : ∀ y, 0 ≤ g y) (n₀ j₀ k : ℕ) (h : Hist E A (j₀ + k)) : 0 ≤ pathReward r g n₀ j₀ k h := by
  rw [pathReward_split]
  have := pathReward_nonneg r hr n₀ j₀ k h
  have := hg (histState (j₀ + k) h)
  linarith

lemma measurable_pathReward (r : ℕ → E × A → ℝ) (g : E → ℝ) (n₀ j₀ k : ℕ)
    (hr : ∀ i < k, Measurable (r (n₀ + i))) (hg : Measurable g) :
    Measurable (pathReward r g n₀ j₀ k) := by
  induction k generalizing g with
  | zero => exact hg.comp (measurable_histState _)
  | succ k ih =>
    have h1 := ih (fun _ => 0) (fun i hi => hr i (by omega)) measurable_const
    have h2 := hr k (by omega)
    change Measurable (fun p : Hist E A (j₀ + k) × A × E =>
      pathReward r (fun _ => 0) n₀ j₀ k p.1 + r (n₀ + k) (histState (j₀ + k) p.1, p.2.1) + g p.2.2)
    exact ((h1.comp measurable_fst).add (h2.comp
      (((measurable_histState _).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)))).add (hg.comp (measurable_snd.comp measurable_snd))

/-- `pathReward` is linear: split the reward into positive and negative parts. -/
lemma pathReward_pos_neg (r : ℕ → E × A → ℝ) (g : E → ℝ) (n₀ j₀ k : ℕ) (h : Hist E A (j₀ + k)) :
    pathReward r g n₀ j₀ k h =
      pathReward (fun k xa => max (r k xa) 0) (fun y => max (g y) 0) n₀ j₀ k h -
      pathReward (fun k xa => max (-r k xa) 0) (fun y => max (-g y) 0) n₀ j₀ k h := by
  induction k generalizing g with
  | zero =>
    simp only [pathReward]
    have := max_zero_sub_max_neg_zero_eq_self (g (histState j₀ h))
    linarith
  | succ k ih =>
    obtain ⟨h1, a, x⟩ := h
    simp only [pathReward]
    have e := ih (fun _ => 0) h1
    simp only [max_self, neg_zero] at e
    rw [e]
    have := max_zero_sub_max_neg_zero_eq_self (r (n₀ + k) (histState (j₀ + k) h1, a))
    have := max_zero_sub_max_neg_zero_eq_self (g x)
    linarith

lemma lintegral_stepKernel (M : MarkovDecisionModel E A N) (m j : ℕ) (hm : m < N)
    (f : Hist E A j → A) (hf : Measurable f) (F : Hist E A (j + 1) → ENNReal) (hF : Measurable F)
    (h : Hist E A j) :
    ∫⁻ y, F y ∂(stepKernel M m j f hf h) =
      ∫⁻ x', F ((h, f h, x') : Hist E A j × A × E) ∂(M.Q m (histState j h, f h)) := by
  have : IsMarkovKernel (M.Q m) := ⟨fun xa => M.hQ_prob m hm xa⟩
  have hmap : Measurable (fun p : Hist E A j × E => ((p.1, f p.1, p.2) : Hist E A (j + 1))) :=
    measurable_fst.prodMk ((hf.comp measurable_fst).prodMk measurable_snd)
  exact (Kernel.lintegral_map _ hmap _ hF).trans (Kernel.lintegral_id_prod (hF.comp hmap) _ _)

lemma isMarkov_pathKernel (M : MarkovDecisionModel E A N) (n₀ j₀ : ℕ)
    (rule : (i : ℕ) → n₀ + i < N → {f : Hist E A (j₀ + i) → A // Measurable f}) :
    ∀ k, n₀ + k ≤ N → IsMarkovKernel (pathKernel M n₀ j₀ rule k) := by
  intro k
  induction k with
  | zero => intro _; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel (Hist E A j₀) _))
  | succ k ih =>
    intro hk
    have hk' : n₀ + k < N := by omega
    have := ih (by omega)
    have : IsMarkovKernel (M.Q (n₀ + k)) := ⟨fun xa => M.hQ_prob _ hk' xa⟩
    rw [show pathKernel M n₀ j₀ rule (k + 1) =
        stepKernel M (n₀ + k) (j₀ + k) (rule k hk').1 (rule k hk').2 ∘ₖ pathKernel M n₀ j₀ rule k
        from dif_pos hk']
    have : IsMarkovKernel (stepKernel M (n₀ + k) (j₀ + k) (rule k hk').1 (rule k hk').2) := by
      unfold stepKernel
      exact Kernel.IsMarkovKernel.map _ (measurable_fst.prodMk
        (((rule k hk').2.comp measurable_fst).prodMk measurable_snd))
    infer_instance

/-- One-step absorption: the last transition of a path is integrated out. -/
lemma absorb (M : MarkovDecisionModel E A N) (r' : ℕ → E × A → ℝ) (hr0 : ∀ k xa, 0 ≤ r' k xa)
    (hrm : ∀ k < N, Measurable (r' k)) (n₀ j₀ : ℕ)
    (rule : (i : ℕ) → n₀ + i < N → {f : Hist E A (j₀ + i) → A // Measurable f})
    (K : ℕ) (hK : n₀ + K < N) (G : E → ENNReal) (hG : Measurable G) (z : Hist E A j₀) :
    ∫⁻ p, (ENNReal.ofReal (pathReward r' (fun _ => 0) n₀ j₀ (K + 1) p) +
        G (histState (j₀ + (K + 1)) p)) ∂(pathKernel M n₀ j₀ rule (K + 1) z) =
    ∫⁻ q, (ENNReal.ofReal (pathReward r' (fun _ => 0) n₀ j₀ K q) +
        (ENNReal.ofReal (r' (n₀ + K) (histState (j₀ + K) q, (rule K hK).1 q)) +
          ∫⁻ y, G y ∂(M.Q (n₀ + K) (histState (j₀ + K) q, (rule K hK).1 q))))
      ∂(pathKernel M n₀ j₀ rule K z) := by
  have : IsMarkovKernel (M.Q (n₀ + K)) := ⟨fun xa => M.hQ_prob _ hK xa⟩
  have hmeas : Measurable (fun p : Hist E A (j₀ + (K + 1)) =>
      ENNReal.ofReal (pathReward r' (fun _ => 0) n₀ j₀ (K + 1) p) +
        G (histState (j₀ + (K + 1)) p)) :=
    (ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
      (fun i hi => hrm _ (by omega)) measurable_const)).add (hG.comp (measurable_histState _))
  rw [show pathKernel M n₀ j₀ rule (K + 1) =
      stepKernel M (n₀ + K) (j₀ + K) (rule K hK).1 (rule K hK).2 ∘ₖ pathKernel M n₀ j₀ rule K
      from dif_pos hK, Kernel.lintegral_comp _ _ _ hmeas]
  refine lintegral_congr fun q => ?_
  refine (lintegral_stepKernel M (n₀ + K) (j₀ + K) hK _ _ _ hmeas q).trans ?_
  have hP := pathReward_nonneg r' hr0 n₀ j₀ K q
  change ∫⁻ x', (ENNReal.ofReal (pathReward r' (fun _ => 0) n₀ j₀ K q +
      r' (n₀ + K) (histState (j₀ + K) q, (rule K hK).1 q) + 0) + G x')
      ∂(M.Q (n₀ + K) (histState (j₀ + K) q, (rule K hK).1 q)) = _
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, add_zero,
    ENNReal.ofReal_add hP (hr0 _ _), add_assoc]

/-! ### Markov policies: reward iteration in `ℝ≥0∞` -/

section Markov

variable (M : MarkovDecisionModel E A N) (r' : ℕ → E × A → ℝ) (g' : E → ℝ)

/-- One application of `T_k^f` to a nonnegative function. -/
noncomputable def T' (k : ℕ) (f : E → A) (G : E → ENNReal) (y : E) : ENNReal :=
  ENNReal.ofReal (r' k (y, f y)) + ∫⁻ y', G y' ∂(M.Q k (y, f y))

/-- Expected reward of `K` Markov steps from time `m`, with terminal function `G`. -/
noncomputable def JM (σ : Policy M) (m K : ℕ) (G : E → ENNReal) (y : E) : ENNReal :=
  ∫⁻ p, (ENNReal.ofReal (pathReward r' (fun _ => 0) m 0 K p) + G (histState (0 + K) p))
    ∂(pathKernel M m 0 (markovRule σ m) K y)

/-- The (nonnegative-part) value of a Markov policy. -/
noncomputable def U (σ : Policy M) (m : ℕ) (y : E) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (pathReward r' g' m 0 (N - m) p)
    ∂(pathKernel M m 0 (markovRule σ m) (N - m) y)

/-- `L_k` applied to `U σ (k+1)`. -/
noncomputable def W (σ : Policy M) (k : ℕ) (xa : E × A) : ENNReal :=
  ENNReal.ofReal (r' k xa) + ∫⁻ y', U M r' g' σ (k + 1) y' ∂(M.Q k xa)

variable (hr0 : ∀ k xa, 0 ≤ r' k xa) (hrm : ∀ k < N, Measurable (r' k))
  (hg0 : ∀ y, 0 ≤ g' y) (hgm : Measurable g')

include hr0 hrm in
lemma measurable_T' (k : ℕ) (hk : k < N) (f : E → A) (hf : Measurable f) (G : E → ENNReal)
    (hG : Measurable G) : Measurable (T' M r' k f G) :=
  (ENNReal.measurable_ofReal.comp ((hrm k hk).comp (measurable_id.prodMk hf))).add
    ((hG.lintegral_kernel (κ := M.Q k)).comp (measurable_id.prodMk hf))

include hr0 hrm in
lemma measurable_JM (σ : Policy M) (m K : ℕ) (hmK : m + K ≤ N) (G : E → ENNReal)
    (hG : Measurable G) : Measurable (JM M r' σ m K G) := by
  refine Measurable.lintegral_kernel ?_
  exact (ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
    (fun i hi => hrm _ (by omega)) measurable_const)).add (hG.comp (measurable_histState _))

include hr0 hrm hg0 hgm in
lemma measurable_U (σ : Policy M) (m : ℕ) : Measurable (U M r' g' σ m) := by
  refine Measurable.lintegral_kernel ?_
  exact ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
    (fun i hi => hrm _ (by omega)) hgm)

include hr0 hrm hg0 hgm in
lemma measurable_W (σ : Policy M) (k : ℕ) (hk : k < N) : Measurable (W M r' g' σ k) :=
  (ENNReal.measurable_ofReal.comp (hrm k hk)).add
    ((measurable_U M r' g' hr0 hrm hg0 hgm σ (k + 1)).lintegral_kernel (κ := M.Q k))

lemma JM_zero (σ : Policy M) (m : ℕ) (G : E → ENNReal) (hG : Measurable G) :
    JM M r' σ m 0 G = G := by
  funext y
  have hmeas : Measurable (fun p : Hist E A (0 + 0) =>
      ENNReal.ofReal (pathReward r' (fun _ => 0) m 0 0 p) + G (histState (0 + 0) p)) :=
    (ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
      (fun i hi => absurd hi (Nat.not_lt_zero _)) measurable_const)).add
      (hG.comp (measurable_histState _))
  unfold JM
  rw [show pathKernel M m 0 (markovRule σ m) 0 = Kernel.id from rfl]
  erw [Kernel.id_apply, lintegral_dirac' _ hmeas]
  simp [pathReward, histState]

include hr0 hrm in
lemma JM_succ (σ : Policy M) (m K : ℕ) (hK : m + K < N) (G : E → ENNReal) (hG : Measurable G) :
    JM M r' σ m (K + 1) G = JM M r' σ m K (T' M r' (m + K) (σ.1 ⟨m + K, hK⟩) G) := by
  funext y
  exact absorb M r' hr0 hrm m 0 (markovRule σ m) K hK G hG y

lemma T'_congr (σ : Policy M) (k k' : ℕ) (e : k = k') (hk : k < N) (hk' : k' < N) :
    T' M r' k (σ.1 ⟨k, hk⟩) = T' M r' k' (σ.1 ⟨k', hk'⟩) := by
  subst e; rfl

include hr0 hrm in
lemma JM_first (σ : Policy M) : ∀ K m (hmK : m + K < N) (G : E → ENNReal), Measurable G →
    JM M r' σ m (K + 1) G = T' M r' m (σ.1 ⟨m, by omega⟩) (JM M r' σ (m + 1) K G) := by
  intro K
  induction K with
  | zero =>
    intro m hm G hG
    rw [JM_succ M r' hr0 hrm σ m 0 hm G hG,
      JM_zero M r' σ m _ (measurable_T' M r' hr0 hrm _ hm _ (σ.2 _).1 G hG),
      JM_zero M r' σ (m + 1) G hG]
    rfl
  | succ K ih =>
    intro m hm G hG
    rw [JM_succ M r' hr0 hrm σ m (K + 1) hm G hG,
      ih m (by omega) _ (measurable_T' M r' hr0 hrm _ hm _ (σ.2 _).1 G hG),
      JM_succ M r' hr0 hrm σ (m + 1) K (by omega) G hG,
      T'_congr M r' σ (m + (K + 1)) (m + 1 + K) (by omega) hm (by omega)]

include hr0 hg0 in
lemma U_eq_JM (σ : Policy M) (m : ℕ) :
    U M r' g' σ m = JM M r' σ m (N - m) (fun y => ENNReal.ofReal (g' y)) := by
  funext y
  unfold U JM
  refine lintegral_congr fun p => ?_
  rw [pathReward_split, ENNReal.ofReal_add (pathReward_nonneg _ hr0 _ _ _ _) (hg0 _)]

include hgm in
lemma U_ge (σ : Policy M) (m : ℕ) (hm : N ≤ m) (y : E) :
    U M r' g' σ m y = ENNReal.ofReal (g' y) := by
  have key : ∀ K (hK : K = 0), ∫⁻ p, ENNReal.ofReal (pathReward r' g' m 0 K p)
      ∂(pathKernel M m 0 (markovRule σ m) K y) = ENNReal.ofReal (g' y) := by
    intro K hK
    subst hK
    rw [show pathKernel M m 0 (markovRule σ m) 0 = Kernel.id from rfl]
    erw [Kernel.id_apply,
      lintegral_dirac' _ (ENNReal.measurable_ofReal.comp (hgm.comp (measurable_histState _)))]
    rfl
  exact key _ (by omega)

include hr0 hrm hg0 hgm in
lemma U_succ (σ : Policy M) (m : ℕ) (hm : m < N) :
    U M r' g' σ m = T' M r' m (σ.1 ⟨m, hm⟩) (U M r' g' σ (m + 1)) := by
  rw [U_eq_JM M r' g' hr0 hg0 σ m, U_eq_JM M r' g' hr0 hg0 σ (m + 1)]
  have e : N - m = (N - (m + 1)) + 1 := by omega
  rw [e]
  exact JM_first M r' hr0 hrm σ (N - (m + 1)) m (by omega) _
    (ENNReal.measurable_ofReal.comp hgm)

lemma U_congr (σ σ' : Policy M) (m : ℕ) (h : ∀ k : Fin N, m ≤ k.val → σ.1 k = σ'.1 k) :
    U M r' g' σ m = U M r' g' σ' m := by
  have : markovRule σ m = markovRule σ' m := by
    funext i hi
    apply Subtype.ext
    funext p
    simp only [markovRule]
    rw [h ⟨m + i, hi⟩ (by simp)]
  unfold U
  rw [this]

end Markov

/-! ### Updating one decision rule of a Markov policy -/

/-- Replace the decision rule at time `k`. -/
def upd {M : MarkovDecisionModel E A N} (σ : Policy M) (k : ℕ) (f : E → A)
    (hf : IsDecisionRule M k f) : Policy M :=
  ⟨fun i => if i.val = k then f else σ.1 i, fun i => by
    by_cases h : i.val = k
    · simp only [h, if_true]; exact h ▸ hf
    · simp only [h, if_false]; exact σ.2 i⟩

lemma upd_at {M : MarkovDecisionModel E A N} (σ : Policy M) (k : ℕ) (f : E → A)
    (hf : IsDecisionRule M k f) (hk : k < N) : (upd σ k f hf).1 ⟨k, hk⟩ = f := by
  show (if (⟨k, hk⟩ : Fin N).val = k then f else σ.1 ⟨k, hk⟩) = f
  rw [if_pos rfl]

lemma upd_ne {M : MarkovDecisionModel E A N} (σ : Policy M) (k : ℕ) (f : E → A)
    (hf : IsDecisionRule M k f) (i : Fin N) (hi : i.val ≠ k) : (upd σ k f hf).1 i = σ.1 i := by
  show (if i.val = k then f else σ.1 i) = σ.1 i
  rw [if_neg hi]

section Upd

variable (M : MarkovDecisionModel E A N) (r' : ℕ → E × A → ℝ) (g' : E → ℝ)
  (hr0 : ∀ k xa, 0 ≤ r' k xa) (hrm : ∀ k < N, Measurable (r' k))
  (hg0 : ∀ y, 0 ≤ g' y) (hgm : Measurable g')

lemma W_upd (σ : Policy M) (k : ℕ) (f : E → A) (hf : IsDecisionRule M k f) :
    W M r' g' (upd σ k f hf) k = W M r' g' σ k := by
  have : U M r' g' (upd σ k f hf) (k + 1) = U M r' g' σ (k + 1) :=
    U_congr M r' g' _ _ _ (fun i hi => upd_ne σ k f hf i (by omega))
  funext xa
  unfold W
  rw [this]

include hr0 hrm hg0 hgm in
lemma U_upd (σ : Policy M) (k : ℕ) (hk : k < N) (f : E → A) (hf : IsDecisionRule M k f) (y : E) :
    U M r' g' (upd σ k f hf) k y = W M r' g' σ k (y, f y) := by
  rw [U_succ M r' g' hr0 hrm hg0 hgm _ k hk, upd_at, ← W_upd M r' g' σ k f hf]
  rfl

end Upd

/-! ### Mixed policies: history policy for `K` steps, then Markov -/

section Mix

variable (M : MarkovDecisionModel E A N) (r' : ℕ → E × A → ℝ) (g' : E → ℝ)
  (π : HistPolicy M) (n : ℕ) (h : Hist E A n)

noncomputable def Mix (σ : Policy M) (K : ℕ) : ENNReal :=
  ∫⁻ p, (ENNReal.ofReal (pathReward r' (fun _ => 0) n n K p) +
      U M r' g' σ (n + K) (histState (n + K) p)) ∂(pathKernel M n n (histRule π n) K h)

variable (hr0 : ∀ k xa, 0 ≤ r' k xa) (hrm : ∀ k < N, Measurable (r' k))
  (hg0 : ∀ y, 0 ≤ g' y) (hgm : Measurable g')

include hr0 hrm hg0 hgm in
lemma Mix_succ (σ : Policy M) (K : ℕ) (hK : n + K < N) :
    Mix M r' g' π n h σ (K + 1) =
      ∫⁻ q, (ENNReal.ofReal (pathReward r' (fun _ => 0) n n K q) +
        W M r' g' σ (n + K) (histState (n + K) q, (π ⟨n + K, hK⟩).1 q))
        ∂(pathKernel M n n (histRule π n) K h) := by
  unfold Mix
  rw [absorb M r' hr0 hrm n n (histRule π n) K hK (U M r' g' σ (n + (K + 1)))
    (measurable_U M r' g' hr0 hrm hg0 hgm σ _) h]
  rfl

include hr0 hrm hg0 hgm in
lemma Mix_zero (σ : Policy M) : Mix M r' g' π n h σ 0 = U M r' g' σ n (histState n h) := by
  have hmeas : Measurable (fun p : Hist E A (n + 0) =>
      ENNReal.ofReal (pathReward r' (fun _ => 0) n n 0 p) +
        U M r' g' σ (n + 0) (histState (n + 0) p)) :=
    (ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
      (fun i hi => absurd hi (Nat.not_lt_zero _)) measurable_const)).add
      ((measurable_U M r' g' hr0 hrm hg0 hgm σ _).comp (measurable_histState _))
  unfold Mix
  rw [show pathKernel M n n (histRule π n) 0 = Kernel.id from rfl, Kernel.id_apply,
    lintegral_dirac' _ hmeas]
  simp [pathReward]

include hr0 hg0 hgm in
lemma Mix_top (σ : Policy M) (hn : n ≤ N) :
    Mix M r' g' π n h σ (N - n) =
      ∫⁻ p, ENNReal.ofReal (pathReward r' g' n n (N - n) p)
        ∂(pathKernel M n n (histRule π n) (N - n) h) := by
  unfold Mix
  refine lintegral_congr fun p => ?_
  rw [U_ge M r' g' hgm σ (n + (N - n)) (by omega), pathReward_split r' g' n n (N - n) p,
    ENNReal.ofReal_add (pathReward_nonneg _ hr0 _ _ _ _) (hg0 _)]

end Mix

/-! ### Derandomization -/

lemma histSB [StandardBorelSpace E] [StandardBorelSpace A] :
    ∀ j, StandardBorelSpace (Hist E A j)
  | 0 => (inferInstance : StandardBorelSpace E)
  | j + 1 => by
    have : StandardBorelSpace (Hist E A j) := histSB j
    exact (inferInstance : StandardBorelSpace (Hist E A j × A × E))

lemma ereal_toReal_eq (x : ENNReal) (hx : x ≠ ⊤) : (x : EReal) = ((x.toReal : ℝ) : EReal) := by
  lift x to NNReal using hx
  simp only [ENNReal.coe_toReal]
  exact EReal.coe_nnreal_eq_coe_real x

lemma conv_lt (x y z w : ENNReal) (hx : x ≠ ⊤) (hy : y ≠ ⊤) (hz : z ≠ ⊤) (hw : w ≠ ⊤)
    (h : (x : EReal) + -(y : EReal) < (z : EReal) + -(w : EReal)) : x + w < z + y := by
  rw [ereal_toReal_eq x hx, ereal_toReal_eq y hy, ereal_toReal_eq z hz, ereal_toReal_eq w hw,
    ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff] at h
  rw [← ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.2 ⟨hx, hw⟩) (ENNReal.add_ne_top.2 ⟨hz, hy⟩),
    ENNReal.toReal_add hx hw, ENNReal.toReal_add hz hy]
  linarith

lemma conv_eq (x y z w : ENNReal) (hx : x ≠ ⊤) (hy : y ≠ ⊤) (hz : z ≠ ⊤) (hw : w ≠ ⊤)
    (h : x + w = z + y) : (x : EReal) + -(y : EReal) = (z : EReal) + -(w : EReal) := by
  rw [ereal_toReal_eq x hx, ereal_toReal_eq y hy, ereal_toReal_eq z hz, ereal_toReal_eq w hw,
    ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  have := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add hx hw, ENNReal.toReal_add hz hy] at this
  linarith

lemma pos_part (r : ℝ) : (((r : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal r := by
  rcases le_total r 0 with h | h
  · rw [sup_of_le_right (by exact_mod_cast h), ENNReal.ofReal_of_nonpos h]; simp
  · rw [sup_of_le_left (by exact_mod_cast h)]; simp

lemma neg_part (r : ℝ) : ((-(r : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-r) := by
  rw [← EReal.coe_neg]; exact pos_part (-r)

lemma nonempty_of_prob {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] :
    Nonempty X := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  exact IsProbabilityMeasure.ne_zero ν (Measure.eq_zero_of_isEmpty ν)

lemma mixture {H : Type u} [MeasurableSpace H] [StandardBorelSpace H] [StandardBorelSpace E]
    (μ : Measure H) [IsProbabilityMeasure μ] (s : H → E) (hs : Measurable s)
    (ρ : H → A) (hρ : Measurable ρ) (D : Set (E × A)) (hρD : ∀ p, (s p, ρ p) ∈ D)
    (f0 : E → A) (hf0 : Measurable f0) (hf0D : ∀ y, (y, f0 y) ∈ D) :
    ∃ F : E → unitInterval → A, Measurable (Function.uncurry F) ∧ (∀ y u, (y, F y u) ∈ D) ∧
      ∀ Ψ : E × A → ENNReal, Measurable Ψ →
        ∫⁻ p, Ψ (s p, ρ p) ∂μ = ∫⁻ u, ∫⁻ p, Ψ (s p, F (s p) u) ∂μ ∂volume := by
  classical
  have : Nonempty H := nonempty_of_prob μ
  have hsp : Measurable (fun p => (s p, p)) := hs.prodMk measurable_id
  set ν : Measure (E × H) := μ.map (fun p => (s p, p)) with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hsp.aemeasurable
  obtain ⟨φ, hφm, hφ⟩ := Kernel.exists_measurable_map_eq_unitInterval ν.condKernel
  let F' : E → H → A := fun y p => if s p = y then ρ p else f0 y
  have hF'm : Measurable (Function.uncurry F') :=
    Measurable.ite (measurableSet_eq_fun (hs.comp measurable_snd) measurable_fst)
      (hρ.comp measurable_snd) (hf0.comp measurable_fst)
  refine ⟨fun y u => F' y (φ y u), hF'm.comp (measurable_fst.prodMk hφm), ?_, ?_⟩
  · intro y u
    dsimp only [F']
    split_ifs with he
    · have := hρD (φ y u); rwa [he] at this
    · exact hf0D y
  · intro Ψ hΨ
    have hΨF : Measurable (fun q : E × H => Ψ (q.1, F' q.1 q.2)) :=
      hΨ.comp (measurable_fst.prodMk hF'm)
    have hΨφ : Measurable (fun q : E × unitInterval => Ψ (q.1, F' q.1 (φ q.1 q.2))) :=
      hΨF.comp (measurable_fst.prodMk hφm)
    have hfst : ν.fst = μ.map s := Measure.fst_map_prodMk measurable_id
    calc ∫⁻ p, Ψ (s p, ρ p) ∂μ = ∫⁻ p, Ψ (s p, F' (s p) p) ∂μ := by
          refine lintegral_congr fun p => ?_
          simp [F']
      _ = ∫⁻ q, Ψ (q.1, F' q.1 q.2) ∂ν := (lintegral_map hΨF hsp).symm
      _ = ∫⁻ y, ∫⁻ p, Ψ (y, F' y p) ∂(ν.condKernel y) ∂ν.fst := by
          conv_lhs => rw [← Measure.disintegrate ν ν.condKernel]
          exact Measure.lintegral_compProd hΨF
      _ = ∫⁻ y, ∫⁻ u, Ψ (y, F' y (φ y u)) ∂volume ∂ν.fst := by
          refine lintegral_congr fun y => ?_
          have h1 : Measurable fun p => Ψ (y, F' y p) :=
            hΨF.comp (measurable_const.prodMk measurable_id)
          have h2 : Measurable (φ y) := hφm.comp (measurable_const.prodMk measurable_id)
          rw [← hφ y, lintegral_map h1 h2]
      _ = ∫⁻ u, ∫⁻ y, Ψ (y, F' y (φ y u)) ∂ν.fst ∂volume :=
          lintegral_lintegral_swap hΨφ.aemeasurable
      _ = _ := by
          rw [hfst]
          refine lintegral_congr fun u => ?_
          have h1 : Measurable fun y => Ψ (y, F' y (φ y u)) :=
            hΨφ.comp (measurable_id.prodMk measurable_const)
          rw [lintegral_map h1 hs]

lemma exists_gt_of_lt_lintegral {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (P : X → ENNReal) (c : ENNReal) (hc : c < ∫⁻ u, P u ∂ν) :
    ∃ u, c < P u := by
  by_contra hne
  push Not at hne
  have : ∫⁻ u, P u ∂ν ≤ ∫⁻ _, c ∂ν := lintegral_mono hne
  simp at this
  exact absurd (hc.trans_le this) (lt_irrefl _)

lemma exists_sub_ge {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (P Q : X → ENNReal) (hP : Measurable P) (hQ : Measurable Q) (hPf : ∫⁻ u, P u ∂ν ≠ ⊤) :
    ∃ u, ((∫⁻ u, P u ∂ν : ENNReal) : EReal) + -((∫⁻ u, Q u ∂ν : ENNReal) : EReal) ≤
      (P u : EReal) + -(Q u : EReal) := by
  have : Nonempty X := nonempty_of_prob ν
  by_contra hne
  push Not at hne
  by_cases hb : ∫⁻ u, Q u ∂ν = ⊤
  · have h0 := hne (Classical.arbitrary X)
    rw [hb] at h0
    simp at h0
  · have hPae : ∀ᵐ u ∂ν, P u < ⊤ := ae_lt_top hP hPf
    have hQae : ∀ᵐ u ∂ν, Q u < ⊤ := ae_lt_top hQ hb
    have hlt : ∀ᵐ u ∂ν, P u + ∫⁻ u, Q u ∂ν < ∫⁻ u, P u ∂ν + Q u := by
      filter_upwards [hPae, hQae] with u hPu hQu
      exact conv_lt _ _ _ _ hPu.ne hQu.ne hPf hb (hne u)
    have e1 : ∫⁻ u, (P u + ∫⁻ u, Q u ∂ν) ∂ν = ∫⁻ u, P u ∂ν + ∫⁻ u, Q u ∂ν := by
      rw [lintegral_add_right _ measurable_const]; simp
    have e2 : ∫⁻ u, (∫⁻ u, P u ∂ν + Q u) ∂ν = ∫⁻ u, P u ∂ν + ∫⁻ u, Q u ∂ν := by
      rw [lintegral_add_left measurable_const]; simp
    have := lintegral_strict_mono (f := fun u => P u + ∫⁻ u, Q u ∂ν)
      (g := fun u => ∫⁻ u, P u ∂ν + Q u) (IsProbabilityMeasure.ne_zero ν)
      (measurable_const.add hQ).aemeasurable (by rw [e1]; exact ENNReal.add_ne_top.2 ⟨hPf, hb⟩) hlt
    rw [e1, e2] at this
    exact lt_irrefl _ this

lemma erealIntegral_decomp {X : Type*} [MeasurableSpace X] (μ : Measure X) (R RP RN : X → ℝ)
    (hRP : Measurable RP) (hRN : Measurable RN) (hP0 : ∀ x, 0 ≤ RP x) (hN0 : ∀ x, 0 ≤ RN x)
    (hR : ∀ x, R x = RP x - RN x) (hfin : ∫⁻ x, ENNReal.ofReal (RP x) ∂μ ≠ ⊤) :
    erealIntegral μ (fun x => (R x : EReal)) =
      ((∫⁻ x, ENNReal.ofReal (RP x) ∂μ : ENNReal) : EReal) +
        -((∫⁻ x, ENNReal.ofReal (RN x) ∂μ : ENNReal) : EReal) := by
  unfold erealIntegral
  simp only [pos_part, neg_part]
  have hRm : Measurable R := by
    have : R = fun x => RP x - RN x := funext hR
    rw [this]; exact hRP.sub hRN
  have hpt : ∀ x, ENNReal.ofReal (R x) + ENNReal.ofReal (RN x) =
      ENNReal.ofReal (RP x) + ENNReal.ofReal (-R x) := by
    intro x
    rcases le_total (R x) 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h, zero_add, ← ENNReal.ofReal_add (hP0 x) (by linarith)]
      congr 1; linarith [hR x]
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -R x ≤ 0), add_zero,
        ← ENNReal.ofReal_add h (hN0 x)]
      congr 1; linarith [hR x]
  have hsum : ∫⁻ x, ENNReal.ofReal (R x) ∂μ + ∫⁻ x, ENNReal.ofReal (RN x) ∂μ =
      ∫⁻ x, ENNReal.ofReal (RP x) ∂μ + ∫⁻ x, ENNReal.ofReal (-R x) ∂μ := by
    rw [← lintegral_add_left (show Measurable fun x => ENNReal.ofReal (R x) from
        ENNReal.measurable_ofReal.comp hRm),
      ← lintegral_add_left (show Measurable fun x => ENNReal.ofReal (RP x) from
        ENNReal.measurable_ofReal.comp hRP)]
    exact lintegral_congr hpt
  have hA : ∫⁻ x, ENNReal.ofReal (R x) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_)
    rw [hR x]; linarith [hN0 x]
  by_cases hB : ∫⁻ x, ENNReal.ofReal (-R x) ∂μ = ⊤
  · have hBN : ∫⁻ x, ENNReal.ofReal (RN x) ∂μ = ⊤ := by
      rw [hB, add_top] at hsum
      by_contra hne
      exact (ENNReal.add_ne_top.2 ⟨hA, hne⟩) hsum
    rw [hB, hBN]
    simp
  · have hBN : ∫⁻ x, ENNReal.ofReal (RN x) ∂μ ≠ ⊤ := by
      intro hne
      rw [hne, add_top] at hsum
      exact ENNReal.add_ne_top.2 ⟨hfin, hB⟩ hsum.symm
    exact conv_eq _ _ _ _ hA hB hfin hBN hsum

/-! ### The main argument -/

section Main

variable [StandardBorelSpace E] [StandardBorelSpace A]
  (M : MarkovDecisionModel E A N) (π : HistPolicy M) (n : ℕ) (h : Hist E A n)

/-- Positive and negative parts. -/
def rP (M : MarkovDecisionModel E A N) : ℕ → E × A → ℝ := fun k xa => max (M.r k xa) 0
def gP (M : MarkovDecisionModel E A N) : E → ℝ := fun y => max (M.g y) 0
def rN (M : MarkovDecisionModel E A N) : ℕ → E × A → ℝ := fun k xa => max (-M.r k xa) 0
def gN (M : MarkovDecisionModel E A N) : E → ℝ := fun y => max (-M.g y) 0

lemma rP0 : ∀ k xa, 0 ≤ rP M k xa := fun _ _ => le_max_right _ _
lemma rN0 : ∀ k xa, 0 ≤ rN M k xa := fun _ _ => le_max_right _ _
lemma gP0 : ∀ y, 0 ≤ gP M y := fun _ => le_max_right _ _
lemma gN0 : ∀ y, 0 ≤ gN M y := fun _ => le_max_right _ _
lemma rPm : ∀ k < N, Measurable (rP M k) := fun k hk => (M.hr_meas k hk).max measurable_const
lemma rNm : ∀ k < N, Measurable (rN M k) := fun k hk => (M.hr_meas k hk).neg.max measurable_const
lemma gPm : Measurable (gP M) := M.hg_meas.max measurable_const
lemma gNm : Measurable (gN M) := M.hg_meas.neg.max measurable_const

lemma derand_sign (r' : ℕ → E × A → ℝ) (g' : E → ℝ)
    (hr0 : ∀ k xa, 0 ≤ r' k xa) (hrm : ∀ k < N, Measurable (r' k))
    (hg0 : ∀ y, 0 ≤ g' y) (hgm : Measurable g') (σ : Policy M) (K : ℕ) (hK : n + K < N)
    (F : E → unitInterval → A) (hFm : Measurable (Function.uncurry F))
    (hFu : ∀ u, IsDecisionRule M (n + K) (fun y => F y u))
    (hFΨ : ∀ Ψ : E × A → ENNReal, Measurable Ψ →
      ∫⁻ p, Ψ (histState (n + K) p, (π ⟨n + K, hK⟩).1 p) ∂(pathKernel M n n (histRule π n) K h) =
        ∫⁻ u, ∫⁻ p, Ψ (histState (n + K) p, F (histState (n + K) p) u)
          ∂(pathKernel M n n (histRule π n) K h) ∂volume) :
    (Measurable fun u => Mix M r' g' π n h (upd σ (n + K) (fun y => F y u) (hFu u)) K) ∧
      Mix M r' g' π n h σ (K + 1) =
        ∫⁻ u, Mix M r' g' π n h (upd σ (n + K) (fun y => F y u) (hFu u)) K := by
  have : IsMarkovKernel (pathKernel M n n (histRule π n) K) :=
    isMarkov_pathKernel M n n _ K (by omega)
  have hR0 : Measurable (fun q : Hist E A (n + K) =>
      ENNReal.ofReal (pathReward r' (fun _ => 0) n n K q)) :=
    ENNReal.measurable_ofReal.comp (measurable_pathReward _ _ _ _ _
      (fun i hi => hrm _ (by omega)) measurable_const)
  have hWm := measurable_W M r' g' hr0 hrm hg0 hgm σ (n + K) hK
  have hG : Measurable (fun u => ∫⁻ q, W M r' g' σ (n + K)
      (histState (n + K) q, F (histState (n + K) q) u) ∂(pathKernel M n n (histRule π n) K h)) := by
    have : Measurable (fun uq : unitInterval × Hist E A (n + K) => W M r' g' σ (n + K)
        (histState (n + K) uq.2, F (histState (n + K) uq.2) uq.1)) :=
      hWm.comp (((measurable_histState _).comp measurable_snd).prodMk
        (hFm.comp (((measurable_histState _).comp measurable_snd).prodMk measurable_fst)))
    exact this.lintegral_prod_right'
  have h1 : (fun u => Mix M r' g' π n h (upd σ (n + K) (fun y => F y u) (hFu u)) K) =
      fun u => ∫⁻ q, ENNReal.ofReal (pathReward r' (fun _ => 0) n n K q)
          ∂(pathKernel M n n (histRule π n) K h) +
        ∫⁻ q, W M r' g' σ (n + K) (histState (n + K) q, F (histState (n + K) q) u)
          ∂(pathKernel M n n (histRule π n) K h) := by
    funext u
    unfold Mix
    rw [← lintegral_add_left hR0]
    refine lintegral_congr fun q => ?_
    rw [U_upd M r' g' hr0 hrm hg0 hgm σ (n + K) hK _ (hFu u)]
  refine ⟨by rw [h1]; exact measurable_const.add hG, ?_⟩
  rw [h1, Mix_succ M r' g' π n h hr0 hrm hg0 hgm σ K hK, lintegral_add_left hR0, hFΨ _ hWm,
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- The derandomization step: one history decision rule is replaced by a Markov one, for both
signs simultaneously. -/
lemma derand_step (σ : Policy M) (K : ℕ) (hK : n + K < N) :
    ∃ σu : unitInterval → Policy M,
      (Measurable fun u => Mix M (rP M) (gP M) π n h (σu u) K) ∧
      (Measurable fun u => Mix M (rN M) (gN M) π n h (σu u) K) ∧
      Mix M (rP M) (gP M) π n h σ (K + 1) = ∫⁻ u, Mix M (rP M) (gP M) π n h (σu u) K ∧
      Mix M (rN M) (gN M) π n h σ (K + 1) = ∫⁻ u, Mix M (rN M) (gN M) π n h (σu u) K := by
  have : IsMarkovKernel (pathKernel M n n (histRule π n) K) :=
    isMarkov_pathKernel M n n _ K (by omega)
  have : StandardBorelSpace (Hist E A (n + K)) := histSB _
  obtain ⟨f0, hf0m, hf0D⟩ := M.hD_sel (n + K) hK
  obtain ⟨F, hFm, hFD, hFΨ⟩ := mixture (pathKernel M n n (histRule π n) K h)
    (histState (n + K)) (measurable_histState _) (π ⟨n + K, hK⟩).1 (π ⟨n + K, hK⟩).2.1
    (M.D (n + K)) (π ⟨n + K, hK⟩).2.2 f0 hf0m hf0D
  have hFu : ∀ u, IsDecisionRule M (n + K) (fun y => F y u) := fun u =>
    ⟨hFm.comp (measurable_id.prodMk measurable_const), fun y => hFD y u⟩
  have hP := derand_sign M π n h (rP M) (gP M) (rP0 M) (rPm M) (gP0 M) (gPm M) σ K hK F hFm hFu hFΨ
  have hN := derand_sign M π n h (rN M) (gN M) (rN0 M) (rNm M) (gN0 M) (gNm M) σ K hK F hFm hFu hFΨ
  exact ⟨fun u => upd σ (n + K) (fun y => F y u) (hFu u), hP.1, hN.1, hP.2, hN.2⟩

lemma stepA : ∀ K, n + K ≤ N → ∀ σ : Policy M,
    Mix M (rP M) (gP M) π n h σ K ≤ deltaN M n (histState n h) := by
  intro K
  induction K with
  | zero =>
    intro _ σ
    rw [Mix_zero M _ _ π n h (rP0 M) (rPm M) (gP0 M) (gPm M)]
    exact le_iSup (fun σ : Policy M => ∫⁻ p, ENNReal.ofReal
      (pathReward (fun k xa => max (M.r k xa) 0) (fun y => max (M.g y) 0) n 0 (N - n) p)
      ∂(pathKernel M n 0 (markovRule σ n) (N - n) (histState n h))) σ
  | succ K ih =>
    intro hK σ
    obtain ⟨σu, hmP, -, hP, -⟩ := derand_step M π n h σ K (by omega)
    refine le_of_forall_lt fun c hc => ?_
    rw [hP] at hc
    obtain ⟨u, hu⟩ := exists_gt_of_lt_lintegral volume _ c hc
    exact hu.trans_le (ih (by omega) (σu u))

lemma stepB (hAN : IntegrabilityAssumption M) (hn : n ≤ N) : ∀ K, n + K ≤ N → ∀ σ : Policy M,
    ∃ σ' : Policy M,
      ((Mix M (rP M) (gP M) π n h σ K : ENNReal) : EReal) +
          -((Mix M (rN M) (gN M) π n h σ K : ENNReal) : EReal) ≤
        ((U M (rP M) (gP M) σ' n (histState n h) : ENNReal) : EReal) +
          -((U M (rN M) (gN M) σ' n (histState n h) : ENNReal) : EReal) := by
  intro K
  induction K with
  | zero =>
    intro _ σ
    exact ⟨σ, by rw [Mix_zero M _ _ π n h (rP0 M) (rPm M) (gP0 M) (gPm M),
      Mix_zero M _ _ π n h (rN0 M) (rNm M) (gN0 M) (gNm M)]⟩
  | succ K ih =>
    intro hK σ
    obtain ⟨σu, hmP, hmN, hP, hN⟩ := derand_step M π n h σ K (by omega)
    have hfin : ∫⁻ u, Mix M (rP M) (gP M) π n h (σu u) K ≠ ⊤ := by
      rw [← hP]
      exact ((stepA M π n h (K + 1) hK σ).trans_lt (hAN n hn _)).ne
    obtain ⟨u, hu⟩ := exists_sub_ge volume _ _ hmP hmN hfin
    obtain ⟨σ', h'⟩ := ih (by omega) (σu u)
    exact ⟨σ', by rw [hP, hN]; exact hu.trans h'⟩

/-- The value of a Markov policy in terms of the positive and negative parts. -/
lemma Vpi_eq (hAN : IntegrabilityAssumption M) (hn : n ≤ N) (σ : Policy M) (x : E) :
    Vpi M σ n x = ((U M (rP M) (gP M) σ n x : ENNReal) : EReal) +
      -((U M (rN M) (gN M) σ n x : ENNReal) : EReal) := by
  have hle : U M (rP M) (gP M) σ n x ≤ deltaN M n x :=
    le_iSup (fun σ : Policy M => ∫⁻ p, ENNReal.ofReal
      (pathReward (fun k xa => max (M.r k xa) 0) (fun y => max (M.g y) 0) n 0 (N - n) p)
      ∂(pathKernel M n 0 (markovRule σ n) (N - n) x)) σ
  unfold Vpi
  exact erealIntegral_decomp _ _ _ _
    (measurable_pathReward _ _ _ _ _ (fun i hi => rPm M _ (by omega)) (gPm M))
    (measurable_pathReward _ _ _ _ _ (fun i hi => rNm M _ (by omega)) (gNm M))
    (pathReward_nonneg' _ _ (rP0 M) (gP0 M) _ _ _) (pathReward_nonneg' _ _ (rN0 M) (gN0 M) _ _ _)
    (fun p => pathReward_pos_neg M.r M.g n 0 (N - n) p) (hle.trans_lt (hAN n hn x)).ne

lemma VHist_le (hAN : IntegrabilityAssumption M) (hn : n ≤ N) :
    VHist M π n h ≤ V M n (histState n h) := by
  let σ0 : Policy M := ⟨fun k => Classical.choose (M.hD_sel k k.2),
    fun k => Classical.choose_spec (M.hD_sel k k.2)⟩
  obtain ⟨σ', hσ'⟩ := stepB M π n h hAN hn (N - n) (by omega) σ0
  have hfin := stepA M π n h (N - n) (by omega) σ0
  rw [Mix_top M _ _ π n h (rP0 M) (gP0 M) (gPm M) σ0 hn,
    Mix_top M _ _ π n h (rN0 M) (gN0 M) (gNm M) σ0 hn] at hσ'
  rw [Mix_top M _ _ π n h (rP0 M) (gP0 M) (gPm M) σ0 hn] at hfin
  have hV : VHist M π n h =
      ((∫⁻ p, ENNReal.ofReal (pathReward (rP M) (gP M) n n (N - n) p)
          ∂(pathKernel M n n (histRule π n) (N - n) h) : ENNReal) : EReal) +
        -((∫⁻ p, ENNReal.ofReal (pathReward (rN M) (gN M) n n (N - n) p)
          ∂(pathKernel M n n (histRule π n) (N - n) h) : ENNReal) : EReal) := by
    unfold VHist
    exact erealIntegral_decomp _ _ _ _
      (measurable_pathReward _ _ _ _ _ (fun i hi => rPm M _ (by omega)) (gPm M))
      (measurable_pathReward _ _ _ _ _ (fun i hi => rNm M _ (by omega)) (gNm M))
      (pathReward_nonneg' _ _ (rP0 M) (gP0 M) _ _ _)
      (pathReward_nonneg' _ _ (rN0 M) (gN0 M) _ _ _)
      (fun p => pathReward_pos_neg M.r M.g n n (N - n) p) (hfin.trans_lt (hAN n hn _)).ne
  rw [hV]
  refine hσ'.trans ?_
  rw [← Vpi_eq M n hAN hn σ']
  exact le_iSup (fun σ : Policy M => Vpi M σ n (histState n h)) σ'

/-- A Markov policy viewed as a history-dependent policy. -/
def embed (σ : Policy M) : HistPolicy M := fun k =>
  ⟨fun p => σ.1 k (histState k p), (σ.2 k).1.comp (measurable_histState k),
    fun p => (σ.2 k).2 (histState k p)⟩

lemma VHist_embed (hAN : IntegrabilityAssumption M) (hn : n ≤ N) (σ : Policy M) :
    VHist M (embed M σ) n h = Vpi M σ n (histState n h) := by
  have key : ∀ (r' : ℕ → E × A → ℝ) (g' : E → ℝ) (hr0 : ∀ k xa, 0 ≤ r' k xa)
      (hrm : ∀ k < N, Measurable (r' k)) (hg0 : ∀ y, 0 ≤ g' y) (hgm : Measurable g'),
      ∀ K, n + K ≤ N → Mix M r' g' (embed M σ) n h σ K = U M r' g' σ n (histState n h) := by
    intro r' g' hr0 hrm hg0 hgm K
    induction K with
    | zero => intro _; exact Mix_zero M r' g' _ n h hr0 hrm hg0 hgm σ
    | succ K ih =>
      intro hK
      rw [← ih (by omega), Mix_succ M r' g' _ n h hr0 hrm hg0 hgm σ K (by omega)]
      unfold Mix
      refine lintegral_congr fun q => ?_
      rw [U_succ M r' g' hr0 hrm hg0 hgm σ (n + K) (by omega)]
      rfl
  have hP := key (rP M) (gP M) (rP0 M) (rPm M) (gP0 M) (gPm M) (N - n) (by omega)
  have hN := key (rN M) (gN M) (rN0 M) (rNm M) (gN0 M) (gNm M) (N - n) (by omega)
  rw [Mix_top M _ _ _ n h (rP0 M) (gP0 M) (gPm M) σ hn] at hP
  rw [Mix_top M _ _ _ n h (rN0 M) (gN0 M) (gNm M) σ hn] at hN
  have hle : U M (rP M) (gP M) σ n (histState n h) ≤ deltaN M n (histState n h) :=
    le_iSup (fun σ : Policy M => ∫⁻ p, ENNReal.ofReal
      (pathReward (fun k xa => max (M.r k xa) 0) (fun y => max (M.g y) 0) n 0 (N - n) p)
      ∂(pathKernel M n 0 (markovRule σ n) (N - n) (histState n h))) σ
  unfold VHist
  rw [erealIntegral_decomp _ _ _ _
      (measurable_pathReward _ _ _ _ _ (fun i hi => rPm M _ (by omega)) (gPm M))
      (measurable_pathReward _ _ _ _ _ (fun i hi => rNm M _ (by omega)) (gNm M))
      (pathReward_nonneg' _ _ (rP0 M) (gP0 M) _ _ _)
      (pathReward_nonneg' _ _ (rN0 M) (gN0 M) _ _ _)
      (fun p => pathReward_pos_neg M.r M.g n n (N - n) p)
      (by rw [hP]; exact (hle.trans_lt (hAN n hn _)).ne), hP, hN, Vpi_eq M n hAN hn σ]

end Main

end Thm223Sol

open BauerleRiederMDP.FiniteHorizon in
theorem solution {E A : Type u} [MeasurableSpace E] [MeasurableSpace A]
    [StandardBorelSpace E] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (n : ℕ) (hn : n ≤ N) (h : Hist E A n) :
    V M n (histState n h) = ⨆ π : HistPolicy M, VHist M π n h := by
  apply le_antisymm
  · refine iSup_le fun σ => ?_
    rw [← Thm223Sol.VHist_embed M n h hAN hn σ]
    exact le_iSup (fun π : HistPolicy M => VHist M π n h) _
  · exact iSup_le fun π => Thm223Sol.VHist_le M π n h hAN hn
