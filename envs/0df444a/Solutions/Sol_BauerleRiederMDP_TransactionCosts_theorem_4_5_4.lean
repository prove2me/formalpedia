-- Prove2me | solution 1 for BauerleRiederMDP.TransactionCosts.theorem_4_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T10:49:32.116415+00:00
-- url     : https://prove2.me/submissions/ba942bd1-7637-485b-aa01-0f4680359e70

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Assumptions
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
import Definitions.Def_BauerleRiederMDP_TransactionCosts_admissibleSet
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IsDecisionRule
import Definitions.Def_BauerleRiederMDP_TransactionCosts_eexp
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_transition
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_statePath
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Lop
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_IsPolicy
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Vpi
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_V
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Top
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IM
import Definitions.Def_BauerleRiederMDP_TransactionCosts_bondAfter
import Definitions.Def_BauerleRiederMDP_TransactionCosts_coneAmount
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IsConeRule
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_optimalStock
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_optimalPolicy
import Definitions.Def_BauerleRiederMDP_TransactionCosts_ConcaveOnE
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IncreasingOnE
import Definitions.Def_BauerleRiederMDP_TransactionCosts_HomogeneousOfDegree

set_option autoImplicit false

universe u

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace P76a

open BauerleRiederMDP.TransactionCosts

/-- Child RI: reward iteration (Bauerle-Rieder Thm 2.3.4) for the transaction cost model. -/
def ChildRI : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (M : Market Ω), M.Assumptions →
    ∀ n < M.N, ∀ π : ℕ → ℝ × ℝ → ℝ × ℝ, M.IsPolicy n π → ∀ x ∈ stateSpace,
      M.Vpi π n x = M.Lop n (M.Vpi π (n + 1)) x (π n x)

variable {Ω : Type*} [MeasurableSpace Ω]

lemma statePath_shift (M : Market Ω) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n : ℕ) (x : ℝ × ℝ) (k : ℕ)
    (ω : Ω) : M.statePath π n x (k + 1) ω
      = M.statePath π (n + 1) (M.transition n (π n x) (M.R (n + 1) ω)) k ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show M.transition (n + (k + 1)) (π (n + (k + 1)) (M.statePath π n x (k + 1) ω))
        (M.R (n + (k + 1) + 1) ω) = M.transition (n + 1 + k)
          (π (n + 1 + k) (M.statePath π (n + 1) (M.transition n (π n x) (M.R (n + 1) ω)) k ω))
          (M.R (n + 1 + k + 1) ω)
    rw [ih, show n + (k + 1) = n + 1 + k by omega]

/-- The path from time `n1` as a function of the start and of the disturbance vector. -/
noncomputable def Gp (M : Market Ω) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n1 m : ℕ) :
    ℕ → ℝ × ℝ → (Fin m → ℝ) → ℝ × ℝ
  | 0, y, _ => y
  | k + 1, y, r => M.transition (n1 + k) (π (n1 + k) (Gp M π n1 m k y r))
      (if h : k < m then r ⟨k, h⟩ else 0)

lemma statePath_eq_Gp (M : Market Ω) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n1 m : ℕ) (y : ℝ × ℝ)
    (ω : Ω) : ∀ k, k ≤ m →
      M.statePath π n1 y k ω = Gp M π n1 m k y (fun j => M.R (n1 + j.val + 1) ω)
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := statePath_eq_Gp M π n1 m y ω k (by omega)
    have hk' : k < m := by omega
    simp only [Market.statePath, Gp, dif_pos hk']
    rw [ih]

lemma meas_transition (M : Market Ω) (j : ℕ) :
    Measurable (fun q : (ℝ × ℝ) × ℝ => M.transition j q.1 q.2) := by
  unfold Market.transition; fun_prop

lemma meas_Gp (M : Market Ω) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n1 m : ℕ)
    (hπ : ∀ j < m, Measurable (π (n1 + j))) : ∀ k, k ≤ m →
      Measurable (fun p : (ℝ × ℝ) × (Fin m → ℝ) => Gp M π n1 m k p.1 p.2)
  | 0, _ => measurable_fst
  | k + 1, hk => by
    have ih := meas_Gp M π n1 m hπ k (by omega)
    have hk' : k < m := by omega
    simp only [Gp, dif_pos hk']
    exact (meas_transition M (n1 + k)).comp
      (((hπ k hk').comp ih).prodMk ((measurable_pi_apply _).comp measurable_snd))

lemma Gp_mem (M : Market Ω) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n1 m : ℕ)
    (hi : ∀ j < m, 0 ≤ M.i (n1 + j + 1))
    (hπ : ∀ j < m, ∀ z ∈ stateSpace, π (n1 + j) z ∈ admissibleSet M.c z)
    (y : ℝ × ℝ) (hy : y ∈ stateSpace) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∀ k, k ≤ m → Gp M π n1 m k y r ∈ stateSpace
  | 0, _ => hy
  | k + 1, hk => by
    have hk' : k < m := by omega
    have ih := Gp_mem M π n1 m hi hπ y hy r hr k (by omega)
    obtain ⟨ha1, ha2, -⟩ := hπ k hk' _ ih
    simp only [Gp, dif_pos hk', Market.transition]
    exact ⟨mul_nonneg ha1 (by linarith [hi k hk']), mul_nonneg ha2 (hr _)⟩

lemma eexp_of_nonneg (P : Measure Ω) (f : Ω → EReal) (hf : ∀ ω, 0 ≤ f ω) :
    eexp P f = ((∫⁻ ω, (f ω).toENNReal ∂P : ENNReal) : EReal) := by
  unfold eexp
  have h0 : ∀ ω, (-f ω).toENNReal = 0 := fun ω =>
    EReal.toENNReal_of_nonpos (by rw [EReal.neg_le, neg_zero]; exact hf ω)
  simp [h0]

lemma U_nonneg (M : Market Ω) (hM : M.Assumptions) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ M.U t := by
  obtain ⟨-, -, -, -, -, -, -, hmono, -, -, hhom⟩ := hM
  have hγ : M.γ ≠ 0 := by
    intro h
    have h1 := hhom 2 two_pos 1 zero_le_one
    rw [h, Real.rpow_zero, one_mul, mul_one] at h1
    have h2 := hmono (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 zero_le_two) one_lt_two
    linarith
  have h0 : M.U 0 = 0 := by
    have h1 := hhom 2 two_pos 0 le_rfl
    rw [mul_zero] at h1
    have hne : (2 : ℝ) ^ M.γ ≠ 1 := by
      intro h
      rw [Real.rpow_def_of_pos two_pos, Real.exp_eq_one_iff] at h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (Real.log_pos one_lt_two).ne'
      · exact hγ h
    have h3 : ((2 : ℝ) ^ M.γ - 1) * M.U 0 = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  rw [← h0]
  exact hmono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht

/-- The integrand of the reward iteration, as a function of `R(n+1)` and of `R(n+2..N)`. -/
noncomputable def Hf (M : Market Ω) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n m : ℕ) (x : ℝ × ℝ) (z : ℝ)
    (r : Fin m → ℝ) : ENNReal :=
  ((M.U (max ((Gp M π (n + 1) m m (M.transition n (π n x) z) r).1
    + (Gp M π (n + 1) m m (M.transition n (π n x) z) r).2) 0) : ℝ) : EReal).toENNReal

lemma indep_R (M : Market Ω) (hM : M.Assumptions) (n m : ℕ) (hm : M.N = n + 1 + m) :
    IndepFun (M.R (n + 1)) (fun ω (j : Fin m) => M.R (n + 1 + j.val + 1) ω) M.P := by
  obtain ⟨-, -, -, -, hR, hind, -⟩ := hM
  have hn : n < M.N := by omega
  have hRm : ∀ k : Fin M.N, Measurable ((fun k : Fin M.N => M.R (k.val + 1)) k) := fun k =>
    (hR (k.val + 1) (by omega) (by have := k.isLt; omega)).1
  have h := hind.indepFun_finset ({⟨n, hn⟩} : Finset (Fin M.N))
    (Finset.univ.filter (fun k : Fin M.N => n < k.val))
    (by rw [Finset.disjoint_singleton_left]; simp) hRm
  have hφ : Measurable (fun v : ({⟨n, hn⟩} : Finset (Fin M.N)) → ℝ =>
      v ⟨⟨n, hn⟩, Finset.mem_singleton_self _⟩) := measurable_pi_apply _
  have hψ : Measurable (fun v : (Finset.univ.filter (fun k : Fin M.N => n < k.val)) → ℝ =>
      fun j : Fin m => v ⟨⟨n + 1 + j.val, by have := j.isLt; omega⟩,
        by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  exact (h.comp hφ hψ).congr (Filter.Eventually.of_forall (fun ω => rfl))
    (Filter.Eventually.of_forall (fun ω => rfl))

lemma fub_eq (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (X : Ω → ℝ) (Y : Ω → Fin d → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (F : ℝ → (Fin d → ℝ) → ENNReal) (hF : Measurable (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)) :
    ∫⁻ ω, F (X ω) (Y ω) ∂P = ∫⁻ ω, ∫⁻ ω', F (X ω) (Y ω') ∂P ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have hg : Measurable (fun z => ∫⁻ r, F z r ∂(P.map Y)) := hF.lintegral_prod_right'
  calc ∫⁻ ω, F (X ω) (Y ω) ∂P = ∫⁻ p, F p.1 p.2 ∂(P.map (fun ω => (X ω, Y ω))) :=
        (lintegral_map hF (hX.prodMk hY)).symm
    _ = ∫⁻ p, F p.1 p.2 ∂((P.map X).prod (P.map Y)) := by rw [hmap]
    _ = ∫⁻ z, ∫⁻ r, F z r ∂(P.map Y) ∂(P.map X) := lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ ω, ∫⁻ r, F (X ω) r ∂(P.map Y) ∂P := lintegral_map hg hX
    _ = ∫⁻ ω, ∫⁻ ω', F (X ω) (Y ω') ∂P ∂P := by
        apply lintegral_congr
        intro ω
        exact lintegral_map (hF.comp measurable_prodMk_left) hY

lemma meas_Hf (M : Market Ω) (hM : M.Assumptions) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n m : ℕ)
    (x : ℝ × ℝ) (hπn : Measurable (π n)) (hπm : ∀ j < m, Measurable (π (n + 1 + j))) :
    Measurable (fun p : ℝ × (Fin m → ℝ) => Hf M π n m x p.1 p.2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hcont, -⟩ := hM
  have hTm : Measurable (fun z : ℝ => M.transition n (π n x) z) :=
    (meas_transition M n).comp (measurable_const.prodMk measurable_id)
  have hUt : Continuous (fun t : ℝ => M.U (max t 0)) :=
    hcont.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)
  have hG2 : Measurable (fun p : ℝ × (Fin m → ℝ) =>
      Gp M π (n + 1) m m (M.transition n (π n x) p.1) p.2) :=
    (meas_Gp M π (n + 1) m hπm m le_rfl).comp ((hTm.comp measurable_fst).prodMk measurable_snd)
  have hS : Measurable (fun p : ℝ × (Fin m → ℝ) =>
      (Gp M π (n + 1) m m (M.transition n (π n x) p.1) p.2).1
        + (Gp M π (n + 1) m m (M.transition n (π n x) p.1) p.2).2) := hG2.fst.add hG2.snd
  unfold Hf
  exact (hUt.measurable.comp hS).coe_real_ereal.ereal_toENNReal

theorem childRI : ChildRI := by
  intro Ω _ M hM n hn π hπ x hx
  obtain ⟨m, hm⟩ : ∃ m, M.N = n + 1 + m := ⟨M.N - n - 1, by omega⟩
  have hP : IsProbabilityMeasure M.P := hM.1
  have hi := hM.2.2.2.1
  have hR := hM.2.2.2.2.1
  have hNn : M.N - n = m + 1 := by omega
  have hNn1 : M.N - (n + 1) = m := by omega
  have hπm : ∀ j < m, Measurable (π (n + 1 + j)) := fun j hj =>
    (hπ (n + 1 + j) (by omega) (by omega)).1
  have hπE : ∀ j < m, ∀ z ∈ stateSpace, π (n + 1 + j) z ∈ admissibleSet M.c z := fun j hj =>
    (hπ (n + 1 + j) (by omega) (by omega)).2
  have hiE : ∀ j < m, 0 ≤ M.i (n + 1 + j + 1) := fun j hj => hi (n + 1 + j + 1) (by omega) (by omega)
  have hRpos : ∀ j < m, ∀ ω, 0 ≤ M.R (n + 1 + j + 1) ω := fun j hj ω =>
    ((hR (n + 1 + j + 1) (by omega) (by omega)).2 ω).le
  have hy : ∀ ω, M.transition n (π n x) (M.R (n + 1) ω) ∈ stateSpace := by
    intro ω
    obtain ⟨ha1, ha2, -⟩ := (hπ n le_rfl hn).2 x hx
    have hi1 := hi (n + 1) (by omega) (by omega)
    exact ⟨mul_nonneg ha1 (by linarith), mul_nonneg ha2 ((hR (n + 1) (by omega) (by omega)).2 ω).le⟩
  have hGE : ∀ ω ω', Gp M π (n + 1) m m (M.transition n (π n x) (M.R (n + 1) ω))
      (fun j => M.R (n + 1 + j.val + 1) ω') ∈ stateSpace := fun ω ω' =>
    Gp_mem M π (n + 1) m hiE hπE _ (hy ω) _ (fun j => hRpos j j.isLt ω') m le_rfl
  have hUnn : ∀ t, 0 ≤ t → 0 ≤ M.U t := U_nonneg M hM
  have hXm : Measurable (M.R (n + 1)) := (hR (n + 1) (by omega) (by omega)).1
  have hYm : Measurable (fun ω (j : Fin m) => M.R (n + 1 + j.val + 1) ω) :=
    measurable_pi_lambda _ (fun j => (hR (n + 1 + j.val + 1) (by omega)
      (by have := j.isLt; omega)).1)
  have hHm := meas_Hf M hM π n m x (hπ n le_rfl hn).1 hπm
  have hFub := fub_eq M.P (M.R (n + 1)) (fun ω (j : Fin m) => M.R (n + 1 + j.val + 1) ω)
    hXm hYm (indep_R M hM n m hm) (Hf M π n m x) hHm
  have hL : M.Vpi π n x = ((∫⁻ ω, Hf M π n m x (M.R (n + 1) ω)
      (fun j => M.R (n + 1 + j.val + 1) ω) ∂M.P : ENNReal) : EReal) := by
    unfold Market.Vpi
    rw [eexp_of_nonneg]
    · congr 1
      apply lintegral_congr
      intro ω
      rw [hNn, statePath_shift, statePath_eq_Gp M π (n + 1) m _ ω m le_rfl]
      unfold Hf
      rw [max_eq_left (add_nonneg (hGE ω ω).1 (hGE ω ω).2)]
    · intro ω
      rw [hNn, statePath_shift, statePath_eq_Gp M π (n + 1) m _ ω m le_rfl]
      exact EReal.coe_nonneg.2 (hUnn _ (add_nonneg (hGE ω ω).1 (hGE ω ω).2))
  have hR1 : ∀ ω, M.Vpi π (n + 1) (M.transition n (π n x) (M.R (n + 1) ω))
      = ((∫⁻ ω', Hf M π n m x (M.R (n + 1) ω) (fun j => M.R (n + 1 + j.val + 1) ω') ∂M.P
          : ENNReal) : EReal) := by
    intro ω
    unfold Market.Vpi
    rw [eexp_of_nonneg]
    · congr 1
      apply lintegral_congr
      intro ω'
      rw [hNn1, statePath_eq_Gp M π (n + 1) m _ ω' m le_rfl]
      unfold Hf
      rw [max_eq_left (add_nonneg (hGE ω ω').1 (hGE ω ω').2)]
    · intro ω'
      rw [hNn1, statePath_eq_Gp M π (n + 1) m _ ω' m le_rfl]
      exact EReal.coe_nonneg.2 (hUnn _ (add_nonneg (hGE ω ω').1 (hGE ω ω').2))
  rw [hL, hFub]
  unfold Market.Lop
  rw [eexp_of_nonneg _ _ (fun ω => by rw [hR1 ω]; exact EReal.coe_ennreal_nonneg _)]
  congr 1
  simp_rw [hR1, EReal.toENNReal_coe]

/-! ## Parent glue -/

section Glue

lemma transition_mem (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) (a : ℝ × ℝ)
    (ha1 : 0 ≤ a.1) (ha2 : 0 ≤ a.2) (ω : Ω) : M.transition n a (M.R (n + 1) ω) ∈ stateSpace := by
  have hi := hM.2.2.2.1 (n + 1) (by omega) (by omega)
  have hR := (hM.2.2.2.2.1 (n + 1) (by omega) (by omega)).2 ω
  exact ⟨mul_nonneg ha1 (by linarith), mul_nonneg ha2 hR.le⟩

lemma Lop_mono (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) (v v' : ℝ × ℝ → EReal)
    (h : ∀ y ∈ stateSpace, v y ≤ v' y) (x a : ℝ × ℝ) (ha1 : 0 ≤ a.1) (ha2 : 0 ≤ a.2) :
    M.Lop n v x a ≤ M.Lop n v' x a := by
  unfold Market.Lop eexp
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (lintegral_mono fun ω =>
      EReal.toENNReal_le_toENNReal (h _ (transition_mem M hM n hn a ha1 ha2 ω)))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (lintegral_mono fun ω =>
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2
        (h _ (transition_mem M hM n hn a ha1 ha2 ω))))

lemma Lop_congr (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) (v v' : ℝ × ℝ → EReal)
    (h : ∀ y ∈ stateSpace, v y = v' y) (x a : ℝ × ℝ) (ha1 : 0 ≤ a.1) (ha2 : 0 ≤ a.2) :
    M.Lop n v x a = M.Lop n v' x a :=
  le_antisymm (Lop_mono M hM n hn v v' (fun y hy => (h y hy).le) x a ha1 ha2)
    (Lop_mono M hM n hn v' v (fun y hy => (h y hy).ge) x a ha1 ha2)

lemma congr_all (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N)
    (v v' : ℝ × ℝ → EReal) (h : ∀ y ∈ stateSpace, v y = v' y) :
    M.argmaxPlus n v = M.argmaxPlus n v' ∧ M.argmaxMinus n v = M.argmaxMinus n v' ∧
    M.aPlus n v = M.aPlus n v' ∧ M.aMinus n v = M.aMinus n v' ∧
    M.qPlus n v = M.qPlus n v' ∧ M.qMinus n v = M.qMinus n v' := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  have hP : M.argmaxPlus n v = M.argmaxPlus n v' := by
    have e : ∀ b ∈ Set.Icc (0 : ℝ) 1, M.Lop n v (0, 1) ((1 - M.c) * (1 - b), b)
        = M.Lop n v' (0, 1) ((1 - M.c) * (1 - b), b) := fun b hb =>
      Lop_congr M hM n hn v v' h _ _ (mul_nonneg (by linarith) (by linarith [hb.2])) hb.1
    ext a
    simp only [Market.argmaxPlus, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hb' => by rw [← e b hb', ← e a ha]; exact hb b hb'⟩
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hb' => by rw [e b hb', e a ha]; exact hb b hb'⟩
  have hM' : M.argmaxMinus n v = M.argmaxMinus n v' := by
    have e : ∀ b ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)), M.Lop n v (1, 0) (1 - (1 + M.c) * b, b)
        = M.Lop n v' (1, 0) (1 - (1 + M.c) * b, b) := fun b hb => by
      have h1 : b * (1 + M.c) ≤ 1 := (le_div_iff₀ (by linarith)).1 hb.2
      exact Lop_congr M hM n hn v v' h _ _ (by nlinarith) hb.1
    ext a
    simp only [Market.argmaxMinus, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hb' => by rw [← e b hb', ← e a ha]; exact hb b hb'⟩
    · rintro ⟨ha, hb⟩
      exact ⟨ha, fun b hb' => by rw [e b hb', e a ha]; exact hb b hb'⟩
  have haP : M.aPlus n v = M.aPlus n v' := by unfold Market.aPlus; rw [hP]
  have haM : M.aMinus n v = M.aMinus n v' := by unfold Market.aMinus; rw [hM']
  refine ⟨hP, hM', haP, haM, ?_, ?_⟩
  · unfold Market.qPlus; rw [haP]
  · unfold Market.qMinus; rw [haM]

/-- The backward-induction iterates `W_j = T_{N-j} ⋯ T_{N-1} g`. -/
noncomputable def Wf (M : Market Ω) : ℕ → ℝ × ℝ → EReal
  | 0 => fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)
  | j + 1 => M.Top (M.N - j - 1) (Wf M j)

lemma w_succ (M : Market Ω) (n : ℕ) (hn : n < M.N) :
    Wf M (M.N - n) = M.Top n (Wf M (M.N - (n + 1))) := by
  have e : M.N - n = (M.N - (n + 1)) + 1 := by omega
  rw [e]
  show M.Top (M.N - (M.N - (n + 1)) - 1) (Wf M (M.N - (n + 1))) = _
  congr 1
  omega

lemma W_IM (M : Market Ω) (hP0 : IM M.γ (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) ∧
      UpperSemicontinuousOn (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) stateSpace)
    (hPs : ∀ n < M.N, ∀ v : ℝ × ℝ → EReal, IM M.γ v → UpperSemicontinuousOn v stateSpace →
      IM M.γ (M.Top n v) ∧ UpperSemicontinuousOn (M.Top n v) stateSpace) :
    ∀ j ≤ M.N, IM M.γ (Wf M j) ∧ UpperSemicontinuousOn (Wf M j) stateSpace
  | 0, _ => hP0
  | j + 1, hj => by
    have ih := W_IM M hP0 hPs j (by omega)
    exact hPs (M.N - j - 1) (by omega) _ ih.1 ih.2

lemma VpiN (M : Market Ω) (hM : M.Assumptions) (π : ℕ → ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ)
    (hx : x ∈ stateSpace) : M.Vpi π M.N x = ((M.U (x.1 + x.2) : ℝ) : EReal) := by
  have hP : IsProbabilityMeasure M.P := hM.1
  have hu : (0 : EReal) ≤ ((M.U (x.1 + x.2) : ℝ) : EReal) :=
    EReal.coe_nonneg.2 (U_nonneg M hM _ (add_nonneg hx.1 hx.2))
  unfold Market.Vpi
  simp only [Nat.sub_self, Market.statePath]
  rw [eexp_of_nonneg _ _ (fun _ => hu), lintegral_const, measure_univ, mul_one,
    EReal.coe_toENNReal hu]

lemma Vpi_le_W (M : Market Ω) (hM : M.Assumptions)
    (hRI : ∀ n < M.N, ∀ π : ℕ → ℝ × ℝ → ℝ × ℝ, M.IsPolicy n π → ∀ x ∈ stateSpace,
      M.Vpi π n x = M.Lop n (M.Vpi π (n + 1)) x (π n x)) :
    ∀ j n, n + j = M.N → ∀ π, M.IsPolicy n π → ∀ x ∈ stateSpace,
      M.Vpi π n x ≤ Wf M (M.N - n) x
  | 0, n, hj, π, _, x, hx => by
    subst hj
    rw [VpiN M hM π x hx, Nat.sub_self]
    rfl
  | j + 1, n, hj, π, hπ, x, hx => by
    have hn : n < M.N := by omega
    have hπ1 : M.IsPolicy (n + 1) π := fun k hk hkN => hπ k (by omega) hkN
    have ih := Vpi_le_W M hM hRI j (n + 1) (by omega) π hπ1
    obtain ⟨ha1, ha2, -⟩ := (hπ n le_rfl hn).2 x hx
    rw [hRI n hn π hπ x hx, w_succ M n hn]
    calc M.Lop n (M.Vpi π (n + 1)) x (π n x)
        ≤ M.Lop n (Wf M (M.N - (n + 1))) x (π n x) :=
          Lop_mono M hM n hn _ _ ih x _ ha1 ha2
      _ ≤ M.Top n (Wf M (M.N - (n + 1))) x := by
          unfold Market.Top
          exact le_iSup₂ (f := fun a (_ : a ∈ admissibleSet M.c x) =>
            M.Lop n (Wf M (M.N - (n + 1))) x a) (π n x) ((hπ n le_rfl hn).2 x hx)

lemma bondAfter_nonneg (M : Market Ω) (hM : M.Assumptions) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c))) : 0 ≤ bondAfter M.c x a := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  unfold bondAfter
  split_ifs with h
  · exact add_nonneg hx.1 (mul_nonneg (by linarith) (by linarith))
  · have h1 : (1 + M.c) * (x.1 / (1 + M.c)) = x.1 := mul_div_cancel₀ _ (by linarith)
    have h2 := mul_le_mul_of_nonneg_left ha.2 (by linarith : (0 : ℝ) ≤ 1 + M.c)
    rw [mul_add, h1] at h2
    nlinarith

lemma concave_transfer {v w : ℝ × ℝ → EReal} (h : ∀ x ∈ stateSpace, v x = w x)
    (hw : ConcaveOnE w) : ConcaveOnE v := by
  intro x hx y hy t ht0 ht1
  rw [h x hx, h y hy, h (t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2)
    ⟨add_nonneg (mul_nonneg ht0 hx.1) (mul_nonneg (by linarith) hy.1),
     add_nonneg (mul_nonneg ht0 hx.2) (mul_nonneg (by linarith) hy.2)⟩]
  exact hw x hx y hy t ht0 ht1

lemma inc_transfer {v w : ℝ × ℝ → EReal} (h : ∀ x ∈ stateSpace, v x = w x)
    (hw : IncreasingOnE w) : IncreasingOnE v := by
  intro x hx y hy h1 h2
  rw [h x hx, h y hy]
  exact hw x hx y hy h1 h2

lemma hom_transfer {γ : ℝ} {v w : ℝ × ℝ → EReal} (h : ∀ x ∈ stateSpace, v x = w x)
    (hw : HomogeneousOfDegree γ w) : HomogeneousOfDegree γ v := by
  intro lam hl x hx
  rw [h (lam * x.1, lam * x.2) ⟨mul_nonneg hl.le hx.1, mul_nonneg hl.le hx.2⟩, h x hx]
  exact hw lam hl x hx

/-- The conclusion of child TH for one `n` and `v`. -/
def THc (M : Market Ω) (n : ℕ) (v : ℝ × ℝ → EReal) : Prop :=
  IsGreatest (M.argmaxPlus n v) (M.aPlus n v) ∧
  IsGreatest (M.argmaxMinus n v) (M.aMinus n v) ∧
  M.qMinus n v ≤ M.qPlus n v ∧
  IsDecisionRule M.c (fun x => (bondAfter M.c x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x),
    coneAmount M.c (M.qPlus n v) (M.qMinus n v) x)) ∧
  ∀ x ∈ stateSpace,
    M.Lop n v x (bondAfter M.c x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x),
      coneAmount M.c (M.qPlus n v) (M.qMinus n v) x) = M.Top n v x ∧
    M.Top n v x = ⨆ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
      M.Lop n v x (bondAfter M.c x a, a)

lemma main_C (M : Market Ω) (hM : M.Assumptions)
    (hRI : ∀ n < M.N, ∀ π : ℕ → ℝ × ℝ → ℝ × ℝ, M.IsPolicy n π → ∀ x ∈ stateSpace,
      M.Vpi π n x = M.Lop n (M.Vpi π (n + 1)) x (π n x))
    (hA : ∀ j ≤ M.N, IM M.γ (Wf M j) ∧ UpperSemicontinuousOn (Wf M j) stateSpace)
    (hTH : ∀ n < M.N, ∀ v : ℝ × ℝ → EReal, IM M.γ v → UpperSemicontinuousOn v stateSpace →
      THc M n v) :
    ∀ j n, n + j = M.N → (∀ x ∈ stateSpace, M.V n x = Wf M (M.N - n) x) ∧
      M.IsPolicy n M.optimalPolicy ∧
      ∀ x ∈ stateSpace, M.Vpi M.optimalPolicy n x = Wf M (M.N - n) x
  | 0, n, hj => by
    have hnN : n = M.N := by omega
    subst hnN
    have hpol : M.IsPolicy M.N M.optimalPolicy := fun k hk hkN => absurd hkN (by omega)
    have hVpi : ∀ x ∈ stateSpace, M.Vpi M.optimalPolicy M.N x = Wf M (M.N - M.N) x :=
      fun x hx => by rw [VpiN M hM _ x hx, Nat.sub_self]; rfl
    refine ⟨fun x hx => ?_, hpol, hVpi⟩
    apply le_antisymm
    · unfold Market.V
      exact iSup_le fun π => Vpi_le_W M hM hRI 0 M.N (by omega) π.1 π.2 x hx
    · rw [← hVpi x hx]
      unfold Market.V
      exact le_iSup (fun π : {π : ℕ → ℝ × ℝ → ℝ × ℝ // M.IsPolicy M.N π} => M.Vpi π.1 M.N x)
        ⟨_, hpol⟩
  | j + 1, n, hj => by
    have hn : n < M.N := by omega
    obtain ⟨hV1, hpol1, hVpi1⟩ := main_C M hM hRI hA hTH j (n + 1) (by omega)
    have hAw := hA (M.N - (n + 1)) (by omega)
    obtain ⟨-, -, -, hdec, hatt⟩ := hTH n hn _ hAw.1 hAw.2
    obtain ⟨-, -, -, -, hqP, hqM⟩ :=
      congr_all M hM n hn (M.V (n + 1)) (Wf M (M.N - (n + 1))) hV1
    have hopt : M.optimalPolicy n = fun x => (bondAfter M.c x (coneAmount M.c
        (M.qPlus n (Wf M (M.N - (n + 1)))) (M.qMinus n (Wf M (M.N - (n + 1)))) x),
        coneAmount M.c (M.qPlus n (Wf M (M.N - (n + 1)))) (M.qMinus n (Wf M (M.N - (n + 1)))) x) := by
      funext x
      simp only [Market.optimalPolicy, Market.optimalStock, hqP, hqM]
    have hpol : M.IsPolicy n M.optimalPolicy := by
      intro k hk hkN
      rcases Nat.eq_or_lt_of_le hk with h | h
      · subst h
        rw [hopt]
        exact hdec
      · exact hpol1 k h hkN
    have hVpi : ∀ x ∈ stateSpace, M.Vpi M.optimalPolicy n x = Wf M (M.N - n) x := by
      intro x hx
      obtain ⟨ha1, ha2, -⟩ := (hpol n le_rfl hn).2 x hx
      rw [hRI n hn _ hpol x hx, Lop_congr M hM n hn _ _ hVpi1 x _ ha1 ha2, w_succ M n hn, hopt]
      exact (hatt x hx).1
    refine ⟨fun x hx => ?_, hpol, hVpi⟩
    apply le_antisymm
    · unfold Market.V
      exact iSup_le fun π => Vpi_le_W M hM hRI (j + 1) n hj π.1 π.2 x hx
    · rw [← hVpi x hx]
      unfold Market.V
      exact le_iSup (fun π : {π : ℕ → ℝ × ℝ → ℝ × ℝ // M.IsPolicy n π} => M.Vpi π.1 n x)
        ⟨_, hpol⟩

theorem glue (M : Market Ω) (hM : M.Assumptions)
    (hRI : ∀ n < M.N, ∀ π : ℕ → ℝ × ℝ → ℝ × ℝ, M.IsPolicy n π → ∀ x ∈ stateSpace,
      M.Vpi π n x = M.Lop n (M.Vpi π (n + 1)) x (π n x))
    (hP0 : IM M.γ (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) ∧
      UpperSemicontinuousOn (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) stateSpace)
    (hPs : ∀ n < M.N, ∀ v : ℝ × ℝ → EReal, IM M.γ v → UpperSemicontinuousOn v stateSpace →
      IM M.γ (M.Top n v) ∧ UpperSemicontinuousOn (M.Top n v) stateSpace)
    (hTH : ∀ n < M.N, ∀ v : ℝ × ℝ → EReal, IM M.γ v → UpperSemicontinuousOn v stateSpace →
      THc M n v) :
    (∀ n ≤ M.N, ConcaveOnE (M.V n) ∧ IncreasingOnE (M.V n) ∧
      HomogeneousOfDegree M.γ (M.V n)) ∧
    (∀ x ∈ stateSpace, M.V M.N x = ((M.U (x.1 + x.2) : ℝ) : EReal)) ∧
    (∀ n < M.N, ∀ x ∈ stateSpace,
      M.V n x = ⨆ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
        M.Lop n (M.V (n + 1)) x (bondAfter M.c x a, a)) ∧
    (∀ n < M.N,
      IsGreatest (M.argmaxPlus n (M.V (n + 1))) (M.aPlus n (M.V (n + 1))) ∧
      IsGreatest (M.argmaxMinus n (M.V (n + 1))) (M.aMinus n (M.V (n + 1))) ∧
      M.qMinus n (M.V (n + 1)) ≤ M.qPlus n (M.V (n + 1))) ∧
    M.IsPolicy 0 M.optimalPolicy ∧
    ∀ n ≤ M.N, ∀ x ∈ stateSpace, M.Vpi M.optimalPolicy n x = M.V n x := by
  have hA := W_IM M hP0 hPs
  have hC : ∀ n ≤ M.N, (∀ x ∈ stateSpace, M.V n x = Wf M (M.N - n) x) ∧
      M.IsPolicy n M.optimalPolicy ∧
      ∀ x ∈ stateSpace, M.Vpi M.optimalPolicy n x = Wf M (M.N - n) x :=
    fun n hn => main_C M hM hRI hA hTH (M.N - n) n (by omega)
  refine ⟨?_, ?_, ?_, ?_, (hC 0 (Nat.zero_le _)).2.1,
    fun n hn x hx => ((hC n hn).2.2 x hx).trans ((hC n hn).1 x hx).symm⟩
  · intro n hn
    obtain ⟨⟨-, -, -, hinc, hconc, hhom⟩, -⟩ := hA (M.N - n) (by omega)
    have h := (hC n hn).1
    exact ⟨concave_transfer h hconc, inc_transfer h hinc, hom_transfer h hhom⟩
  · intro x hx
    rw [(hC M.N le_rfl).1 x hx, Nat.sub_self]
    rfl
  · intro n hn x hx
    have hAw := hA (M.N - (n + 1)) (by omega)
    obtain ⟨-, -, -, -, hatt⟩ := hTH n hn _ hAw.1 hAw.2
    rw [(hC n hn.le).1 x hx, w_succ M n hn, (hatt x hx).2]
    refine iSup_congr fun a => iSup_congr fun ha => ?_
    exact Lop_congr M hM n hn _ _ (fun y hy => ((hC (n + 1) hn).1 y hy).symm) x _
      (bondAfter_nonneg M hM x hx a ha) ha.1
  · intro n hn
    have hAw := hA (M.N - (n + 1)) (by omega)
    obtain ⟨hgP, hgM, hq, -⟩ := hTH n hn _ hAw.1 hAw.2
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ :=
      congr_all M hM n hn (M.V (n + 1)) (Wf M (M.N - (n + 1))) (hC (n + 1) hn).1
    rw [e1, e2, e3, e4, e5, e6]
    exact ⟨hgP, hgM, hq⟩

end Glue
end P76a

namespace P76a

open BauerleRiederMDP.TransactionCosts

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## TH layer 1: basic facts on `IM` functions and `Lop` -/

lemma th_gamma_ne_zero (M : Market Ω) (hM : M.Assumptions) : M.γ ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, hmono, -, -, hhom⟩ := hM
  intro h
  have h1 := hhom 2 two_pos 1 zero_le_one
  rw [h, Real.rpow_zero, one_mul, mul_one] at h1
  have h2 := hmono (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 zero_le_two) one_lt_two
  linarith

lemma th_two_rpow_ne_one {γ : ℝ} (hγ : γ ≠ 0) : (2 : ℝ) ^ γ ≠ 1 := by
  intro h
  rw [Real.rpow_def_of_pos two_pos, Real.exp_eq_one_iff] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (Real.log_pos one_lt_two).ne'
  · exact hγ h

lemma th_zero_mem : ((0 : ℝ), (0 : ℝ)) ∈ stateSpace := ⟨le_rfl, le_rfl⟩

lemma th_IM_ne_top {γ : ℝ} {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    v x ≠ ⊤ := by
  obtain ⟨C, -, hC⟩ := hv.2.2.1
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (hC x hx)

lemma th_IM_coe {γ : ℝ} {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    v x = (((v x).toReal : ℝ) : EReal) :=
  (EReal.coe_toReal (th_IM_ne_top hv x hx) (hv.2.1 x hx)).symm

lemma th_IM_zero {γ : ℝ} (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) : v (0, 0) = 0 := by
  have h1 := hv.2.2.2.2.2 2 two_pos (0, 0) th_zero_mem
  simp only [mul_zero] at h1
  rw [th_IM_coe hv _ th_zero_mem, ← EReal.coe_mul] at h1
  have h2 := EReal.coe_injective h1
  have h3 : ((2 : ℝ) ^ γ - 1) * (v (0, 0)).toReal = 0 := by
    rw [sub_mul, one_mul, ← h2, sub_self]
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) (th_two_rpow_ne_one hγ)
  · rw [th_IM_coe hv _ th_zero_mem, h]; rfl

lemma th_IM_nonneg {γ : ℝ} (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ)
    (hx : x ∈ stateSpace) : 0 ≤ v x := by
  rw [← th_IM_zero hγ hv]
  exact hv.2.2.2.1 _ th_zero_mem x hx hx.1 hx.2

/-- Real-valued version of an `IM` function. -/
noncomputable def vr (v : ℝ × ℝ → EReal) (x : ℝ × ℝ) : ℝ := (v x).toReal

lemma vr_nonneg {γ : ℝ} (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ)
    (hx : x ∈ stateSpace) : 0 ≤ vr v x :=
  EReal.toReal_nonneg (th_IM_nonneg hγ hv x hx)

lemma vr_mono {γ : ℝ} {v : ℝ × ℝ → EReal} (hv : IM γ v) (x y : ℝ × ℝ) (hx : x ∈ stateSpace)
    (hy : y ∈ stateSpace) (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) : vr v x ≤ vr v y := by
  have h := hv.2.2.2.1 x hx y hy h1 h2
  rw [th_IM_coe hv x hx, th_IM_coe hv y hy] at h
  exact EReal.coe_le_coe_iff.1 h

lemma vr_concave {γ : ℝ} {v : ℝ × ℝ → EReal} (hv : IM γ v) (x y : ℝ × ℝ) (hx : x ∈ stateSpace)
    (hy : y ∈ stateSpace) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * vr v x + (1 - t) * vr v y ≤ vr v (t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2) := by
  have hz : ((t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2) : ℝ × ℝ) ∈ stateSpace :=
    ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2, hy.2]⟩
  have h := hv.2.2.2.2.1 x hx y hy t ht0 ht1
  rw [th_IM_coe hv x hx, th_IM_coe hv y hy, th_IM_coe hv _ hz, ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.1 h

lemma vr_hom {γ : ℝ} {v : ℝ × ℝ → EReal} (hv : IM γ v) (lam : ℝ) (hl : 0 < lam) (x : ℝ × ℝ)
    (hx : x ∈ stateSpace) : vr v (lam * x.1, lam * x.2) = lam ^ γ * vr v x := by
  have h := hv.2.2.2.2.2 lam hl x hx
  have hz : ((lam * x.1, lam * x.2) : ℝ × ℝ) ∈ stateSpace :=
    ⟨mul_nonneg hl.le hx.1, mul_nonneg hl.le hx.2⟩
  rw [th_IM_coe hv x hx, th_IM_coe hv _ hz, ← EReal.coe_mul] at h
  exact EReal.coe_injective h

lemma vr_bound {γ : ℝ} {v : ℝ × ℝ → EReal} (hv : IM γ v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ stateSpace, vr v x ≤ C * (1 + x.1 + x.2) := by
  obtain ⟨C, hC0, hC⟩ := hv.2.2.1
  refine ⟨C, hC0, fun x hx => ?_⟩
  have h := hC x hx
  rw [th_IM_coe hv x hx] at h
  exact EReal.coe_le_coe_iff.1 h

lemma th_transition_mem (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) (a : ℝ × ℝ)
    (ha1 : 0 ≤ a.1) (ha2 : 0 ≤ a.2) (ω : Ω) : M.transition n a (M.R (n + 1) ω) ∈ stateSpace := by
  have hi := hM.2.2.2.1 (n + 1) (by omega) (by omega)
  have hR := (hM.2.2.2.2.1 (n + 1) (by omega) (by omega)).2 ω
  exact ⟨mul_nonneg ha1 (by linarith), mul_nonneg ha2 hR.le⟩

lemma th_meas_comp (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    {v : ℝ × ℝ → EReal} (hv : IM γ v) (a : ℝ × ℝ) (ha1 : 0 ≤ a.1) (ha2 : 0 ≤ a.2) :
    Measurable (fun ω => vr v (M.transition n a (M.R (n + 1) ω))) := by
  have hR := (hM.2.2.2.2.1 (n + 1) (by omega) (by omega)).1
  have hT : Measurable (fun ω => M.transition n a (M.R (n + 1) ω)) := by
    unfold Market.transition
    exact measurable_const.prodMk (measurable_const.mul hR)
  have hS : Measurable (fun ω => (⟨M.transition n a (M.R (n + 1) ω),
      th_transition_mem M hM n hn a ha1 ha2 ω⟩ : stateSpace)) := hT.subtype_mk
  exact measurable_ereal_toReal.comp (hv.1.comp hS)

lemma th_integrable (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (a : ℝ × ℝ) (ha1 : 0 ≤ a.1)
    (ha2 : 0 ≤ a.2) : Integrable (fun ω => vr v (M.transition n a (M.R (n + 1) ω))) M.P := by
  have := hM.1
  obtain ⟨C, hC0, hC⟩ := vr_bound hv
  have hRi := hM.2.2.2.2.2.2.1 (n + 1) (by omega) (by omega)
  have hg : Integrable (fun ω => C * (1 + a.1 * (1 + M.i (n + 1)) + a.2 * M.R (n + 1) ω)) M.P :=
    ((integrable_const _).add (hRi.const_mul a.2)).const_mul C
  refine hg.mono' (th_meas_comp M hM n hn hv a ha1 ha2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hm := th_transition_mem M hM n hn a ha1 ha2 ω
  rw [Real.norm_of_nonneg (vr_nonneg hγ hv _ hm)]
  exact hC _ hm

/-- The real expectation `G a = E v(transition a R)`. -/
noncomputable def G (M : Market Ω) (n : ℕ) (v : ℝ × ℝ → EReal) (a : ℝ × ℝ) : ℝ :=
  ∫ ω, vr v (M.transition n a (M.R (n + 1) ω)) ∂M.P

lemma Lop_eq_G (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (x a : ℝ × ℝ) (ha1 : 0 ≤ a.1)
    (ha2 : 0 ≤ a.2) : M.Lop n v x a = ((G M n v a : ℝ) : EReal) := by
  have hI := th_integrable M hM n hn hγ hv a ha1 ha2
  have hnn : ∀ ω, 0 ≤ vr v (M.transition n a (M.R (n + 1) ω)) := fun ω =>
    vr_nonneg hγ hv _ (th_transition_mem M hM n hn a ha1 ha2 ω)
  have h0 : ∀ ω, (-v (M.transition n a (M.R (n + 1) ω))).toENNReal = 0 := fun ω =>
    EReal.toENNReal_of_nonpos (by
      rw [EReal.neg_le, neg_zero]
      exact th_IM_nonneg hγ hv _ (th_transition_mem M hM n hn a ha1 ha2 ω))
  have h1 : ∀ ω, (v (M.transition n a (M.R (n + 1) ω))).toENNReal =
      ENNReal.ofReal (vr v (M.transition n a (M.R (n + 1) ω))) := fun ω => by
    rw [th_IM_coe hv _ (th_transition_mem M hM n hn a ha1 ha2 ω)]
    rfl
  unfold Market.Lop eexp G
  simp only [h0, lintegral_zero, h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hnn)]
  have hI0 : (0 : ℝ) ≤ ∫ ω, vr v (M.transition n a (M.R (n + 1) ω)) ∂M.P :=
    integral_nonneg (fun ω => hnn ω)
  simp [EReal.coe_ennreal_ofReal, max_eq_left hI0]

/-! ## TH layer 2: `G` is monotone, concave, homogeneous; `Top` is a sup over the frontier -/

lemma th_trans_le (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) (a b : ℝ × ℝ)
    (h1 : a.1 ≤ b.1) (h2 : a.2 ≤ b.2) (ω : Ω) :
    (M.transition n a (M.R (n + 1) ω)).1 ≤ (M.transition n b (M.R (n + 1) ω)).1 ∧
    (M.transition n a (M.R (n + 1) ω)).2 ≤ (M.transition n b (M.R (n + 1) ω)).2 := by
  have hi := hM.2.2.2.1 (n + 1) (by omega) (by omega)
  have hR := (hM.2.2.2.2.1 (n + 1) (by omega) (by omega)).2 ω
  exact ⟨mul_le_mul_of_nonneg_right h1 (by linarith), mul_le_mul_of_nonneg_right h2 hR.le⟩

lemma G_mono (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (a b : ℝ × ℝ) (ha1 : 0 ≤ a.1)
    (ha2 : 0 ≤ a.2) (h1 : a.1 ≤ b.1) (h2 : a.2 ≤ b.2) : G M n v a ≤ G M n v b := by
  unfold G
  refine integral_mono (th_integrable M hM n hn hγ hv a ha1 ha2)
    (th_integrable M hM n hn hγ hv b (ha1.trans h1) (ha2.trans h2)) (fun ω => ?_)
  have h := th_trans_le M hM n hn a b h1 h2 ω
  exact vr_mono hv _ _ (th_transition_mem M hM n hn a ha1 ha2 ω)
    (th_transition_mem M hM n hn b (ha1.trans h1) (ha2.trans h2) ω) h.1 h.2

lemma G_concave (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (a b : ℝ × ℝ) (ha1 : 0 ≤ a.1)
    (ha2 : 0 ≤ a.2) (hb1 : 0 ≤ b.1) (hb2 : 0 ≤ b.2) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * G M n v a + (1 - t) * G M n v b ≤
      G M n v (t * a.1 + (1 - t) * b.1, t * a.2 + (1 - t) * b.2) := by
  have hIa := th_integrable M hM n hn hγ hv a ha1 ha2
  have hIb := th_integrable M hM n hn hγ hv b hb1 hb2
  have hc1 : 0 ≤ t * a.1 + (1 - t) * b.1 := by nlinarith
  have hc2 : 0 ≤ t * a.2 + (1 - t) * b.2 := by nlinarith
  unfold G
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hIa.const_mul t)
    (hIb.const_mul (1 - t))]
  refine integral_mono ((hIa.const_mul t).add (hIb.const_mul (1 - t)))
    (th_integrable M hM n hn hγ hv _ hc1 hc2) (fun ω => ?_)
  have hT : M.transition n (t * a.1 + (1 - t) * b.1, t * a.2 + (1 - t) * b.2) (M.R (n + 1) ω) =
      (t * (M.transition n a (M.R (n + 1) ω)).1 + (1 - t) * (M.transition n b (M.R (n + 1) ω)).1,
       t * (M.transition n a (M.R (n + 1) ω)).2 + (1 - t) * (M.transition n b (M.R (n + 1) ω)).2) := by
    unfold Market.transition
    ext <;> simp <;> ring
  simp only
  rw [hT]
  exact vr_concave hv _ _ (th_transition_mem M hM n hn a ha1 ha2 ω)
    (th_transition_mem M hM n hn b hb1 hb2 ω) t ht0 ht1

lemma G_hom (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    {v : ℝ × ℝ → EReal} (hv : IM γ v) (lam : ℝ) (hl : 0 < lam) (a : ℝ × ℝ) (ha1 : 0 ≤ a.1)
    (ha2 : 0 ≤ a.2) : G M n v (lam * a.1, lam * a.2) = lam ^ γ * G M n v a := by
  unfold G
  rw [← integral_const_mul]
  congr 1
  funext ω
  have hT : M.transition n (lam * a.1, lam * a.2) (M.R (n + 1) ω) =
      (lam * (M.transition n a (M.R (n + 1) ω)).1, lam * (M.transition n a (M.R (n + 1) ω)).2) := by
    unfold Market.transition
    ext <;> simp <;> ring
  rw [hT]
  exact vr_hom hv lam hl _ (th_transition_mem M hM n hn a ha1 ha2 ω)

lemma th_bondAfter_nonneg (M : Market Ω) (hM : M.Assumptions) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c))) : 0 ≤ bondAfter M.c x a := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  unfold bondAfter
  split_ifs with h
  · exact add_nonneg hx.1 (mul_nonneg (by linarith) (by linarith))
  · have h1 : (1 + M.c) * (x.1 / (1 + M.c)) = x.1 := mul_div_cancel₀ _ (by linarith)
    have h2 := mul_le_mul_of_nonneg_left ha.2 (by linarith : (0 : ℝ) ≤ 1 + M.c)
    rw [mul_add, h1] at h2
    nlinarith

lemma th_frontier_adm (M : Market Ω) (hM : M.Assumptions) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c))) :
    ((bondAfter M.c x a, a) : ℝ × ℝ) ∈ admissibleSet M.c x := by
  refine ⟨th_bondAfter_nonneg M hM x hx a ha, ha.1, ?_⟩
  simp only
  unfold bondAfter
  split_ifs with h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma th_adm_frontier (M : Market Ω) (hM : M.Assumptions) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (a : ℝ × ℝ)
    (ha : a ∈ admissibleSet M.c x) :
    a.1 ≤ bondAfter M.c x a.2 ∧ a.2 ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)) := by
  obtain ⟨h1, h2, h3⟩ := ha
  have hc0 := hM.2.1
  have hb : a.1 ≤ bondAfter M.c x a.2 := by
    unfold bondAfter
    split_ifs with h
    · rw [abs_of_nonpos (by linarith)] at h3; linarith
    · rw [abs_of_pos (by linarith)] at h3; linarith
  refine ⟨hb, h2, ?_⟩
  by_cases h : a.2 ≤ x.2
  · have : 0 ≤ x.1 / (1 + M.c) := div_nonneg hx.1 (by linarith)
    linarith
  · rw [abs_of_pos (by linarith)] at h3
    have : a.2 - x.2 ≤ x.1 / (1 + M.c) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + M.c)]; nlinarith
    linarith

lemma Top_frontier (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    M.Top n v x = ⨆ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
      M.Lop n v x (bondAfter M.c x a, a) := by
  unfold Market.Top
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    obtain ⟨hb, hI⟩ := th_adm_frontier M hM x hx a ha
    refine le_iSup₂_of_le a.2 hI ?_
    rw [Lop_eq_G M hM n hn hγ hv x a ha.1 ha.2.1,
      Lop_eq_G M hM n hn hγ hv x (bondAfter M.c x a.2, a.2) (th_bondAfter_nonneg M hM x hx _ hI)
        hI.1]
    exact EReal.coe_le_coe_iff.2 (G_mono M hM n hn hγ hv a _ ha.1 ha.2.1 hb le_rfl)
  · exact iSup₂_le fun a ha => le_iSup₂_of_le (f := fun a _ => M.Lop n v x a) _
      (th_frontier_adm M hM x hx a ha) le_rfl

/-! ## TH layer 3: sequential upper semicontinuity of `G`, largest maximizers exist -/

lemma G_nonneg (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (a : ℝ × ℝ) (ha1 : 0 ≤ a.1)
    (ha2 : 0 ≤ a.2) : 0 ≤ G M n v a :=
  integral_nonneg fun ω => vr_nonneg hγ hv _ (th_transition_mem M hM n hn a ha1 ha2 ω)

lemma G_ofReal (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (a : ℝ × ℝ) (ha1 : 0 ≤ a.1)
    (ha2 : 0 ≤ a.2) : ENNReal.ofReal (G M n v a) =
      ∫⁻ ω, ENNReal.ofReal (vr v (M.transition n a (M.R (n + 1) ω))) ∂M.P :=
  ofReal_integral_eq_lintegral_ofReal (th_integrable M hM n hn hγ hv a ha1 ha2)
    (Filter.Eventually.of_forall fun ω =>
      vr_nonneg hγ hv _ (th_transition_mem M hM n hn a ha1 ha2 ω))

lemma G_usc_seq (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (husc : UpperSemicontinuousOn v stateSpace)
    (a : ℕ → ℝ × ℝ) (b : ℝ × ℝ) (ha1 : ∀ k, (a k).1 ∈ Set.Icc (0 : ℝ) 1)
    (ha2 : ∀ k, (a k).2 ∈ Set.Icc (0 : ℝ) 1) (hb1 : 0 ≤ b.1) (hb2 : 0 ≤ b.2)
    (hab : Filter.Tendsto a Filter.atTop (nhds b)) (L : ℝ)
    (hL : Filter.Tendsto (fun k => G M n v (a k)) Filter.atTop (nhds L)) : L ≤ G M n v b := by
  have := hM.1
  obtain ⟨C, hC0, hC⟩ := vr_bound hv
  have hi := hM.2.2.2.1 (n + 1) (by omega) (by omega)
  have hRi := hM.2.2.2.2.2.2.1 (n + 1) (by omega) (by omega)
  have hRpos := (hM.2.2.2.2.1 (n + 1) (by omega) (by omega)).2
  have hgI : Integrable (fun ω => C * (2 + M.i (n + 1) + M.R (n + 1) ω)) M.P :=
    ((integrable_const (2 + M.i (n + 1))).add hRi).const_mul C
  have hlim : Filter.limsup (fun k => ENNReal.ofReal (G M n v (a k))) Filter.atTop =
      ENNReal.ofReal L :=
    ((ENNReal.continuous_ofReal.tendsto L).comp hL).limsup_eq
  have hpt : ∀ ω, Filter.limsup (fun k => ENNReal.ofReal (vr v (M.transition n (a k)
      (M.R (n + 1) ω)))) Filter.atTop ≤ ENNReal.ofReal (vr v (M.transition n b (M.R (n + 1) ω))) := by
    intro ω
    have hmem := th_transition_mem M hM n hn b hb1 hb2 ω
    have hT : Filter.Tendsto (fun k => M.transition n (a k) (M.R (n + 1) ω)) Filter.atTop
        (nhdsWithin (M.transition n b (M.R (n + 1) ω)) stateSpace) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun k =>
        th_transition_mem M hM n hn (a k) (ha1 k).1 (ha2 k).1 ω⟩
      have hc : Continuous (fun p : ℝ × ℝ => M.transition n p (M.R (n + 1) ω)) := by
        unfold Market.transition
        exact (continuous_fst.mul continuous_const).prodMk (continuous_snd.mul continuous_const)
      exact (hc.tendsto b).comp hab
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set t := vr v (M.transition n b (M.R (n + 1) ω))
    have hy : v (M.transition n b (M.R (n + 1) ω)) < ((t + ε : ℝ) : EReal) := by
      rw [th_IM_coe hv _ hmem]
      exact EReal.coe_lt_coe_iff.2 (by simp only [t, vr]; linarith [ε.2, (NNReal.coe_pos.2 hε)])
    have hev := hT.eventually (husc _ hmem _ hy)
    refine Filter.limsup_le_of_le (by isBoundedDefault) (hev.mono fun k hk => ?_)
    have hk0 : v (M.transition n (a k) (M.R (n + 1) ω)) < ((t + ε : ℝ) : EReal) := hk
    rw [th_IM_coe hv _ (th_transition_mem M hM n hn (a k) (ha1 k).1 (ha2 k).1 ω)] at hk0
    have hk' := EReal.coe_lt_coe_iff.1 hk0
    calc ENNReal.ofReal (vr v (M.transition n (a k) (M.R (n + 1) ω)))
        ≤ ENNReal.ofReal (t + ε) := ENNReal.ofReal_le_ofReal hk'.le
      _ = ENNReal.ofReal t + ε := by
        rw [ENNReal.ofReal_add (show (0 : ℝ) ≤ t from vr_nonneg hγ hv _ hmem) (NNReal.coe_nonneg ε),
          ENNReal.ofReal_coe_nnreal]
  have hfat := limsup_lintegral_le (μ := M.P)
    (f := fun k ω => ENNReal.ofReal (vr v (M.transition n (a k) (M.R (n + 1) ω))))
    (fun ω => ENNReal.ofReal (C * (2 + M.i (n + 1) + M.R (n + 1) ω)))
    (fun k => ENNReal.measurable_ofReal.comp
      (th_meas_comp M hM n hn hv (a k) (ha1 k).1 (ha2 k).1))
    (fun k => Filter.Eventually.of_forall fun ω => by
      have hm := th_transition_mem M hM n hn (a k) (ha1 k).1 (ha2 k).1 ω
      refine ENNReal.ofReal_le_ofReal ((hC _ hm).trans (mul_le_mul_of_nonneg_left ?_ hC0))
      have e1 : (M.transition n (a k) (M.R (n + 1) ω)).1 = (a k).1 * (1 + M.i (n + 1)) := rfl
      have e2 : (M.transition n (a k) (M.R (n + 1) ω)).2 = (a k).2 * M.R (n + 1) ω := rfl
      rw [e1, e2]
      obtain ⟨h1a, h1b⟩ := ha1 k
      obtain ⟨h2a, h2b⟩ := ha2 k
      have hR0 := hRpos ω
      nlinarith [mul_nonneg (sub_nonneg.2 h1b) (by linarith : (0 : ℝ) ≤ 1 + M.i (n + 1)),
        mul_nonneg (sub_nonneg.2 h2b) hR0.le])
    hgI.lintegral_lt_top.ne
  have hmain : ENNReal.ofReal L ≤ ENNReal.ofReal (G M n v b) := by
    rw [← hlim, G_ofReal M hM n hn hγ hv b hb1 hb2]
    simp_rw [G_ofReal M hM n hn hγ hv _ (ha1 _).1 (ha2 _).1]
    exact hfat.trans (lintegral_mono hpt)
  exact (ENNReal.ofReal_le_ofReal_iff (G_nonneg M hM n hn hγ hv b hb1 hb2)).1 hmain

/-- Abstract: a sequentially usc function on `[0,B]` has a largest maximizer. -/
lemma isGreatest_argmax (g : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hbdd : BddAbove (g '' Set.Icc 0 B))
    (husc : ∀ (b : ℕ → ℝ) (x L : ℝ), (∀ k, b k ∈ Set.Icc 0 B) →
      Filter.Tendsto b Filter.atTop (nhds x) →
      Filter.Tendsto (fun k => g (b k)) Filter.atTop (nhds L) → L ≤ g x) :
    IsGreatest {a | a ∈ Set.Icc (0 : ℝ) B ∧ ∀ b ∈ Set.Icc (0 : ℝ) B, g b ≤ g a}
      (sSup {a | a ∈ Set.Icc (0 : ℝ) B ∧ ∀ b ∈ Set.Icc (0 : ℝ) B, g b ≤ g a}) := by
  set S := {a | a ∈ Set.Icc (0 : ℝ) B ∧ ∀ b ∈ Set.Icc (0 : ℝ) B, g b ≤ g a}
  set m := sSup (g '' Set.Icc 0 B)
  have hne : (g '' Set.Icc 0 B).Nonempty := ⟨g 0, 0, ⟨le_rfl, hB⟩, rfl⟩
  have hle : ∀ y ∈ Set.Icc (0 : ℝ) B, g y ≤ m := fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
  have hS : ∀ x ∈ Set.Icc (0 : ℝ) B, m ≤ g x → x ∈ S := fun x hx hm =>
    ⟨hx, fun y hy => (hle y hy).trans hm⟩
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup hne hbdd
  choose b hb hgb using hmem
  obtain ⟨x, hx, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hb
  have hgx : m ≤ g x := husc (b ∘ φ) x m (fun k => hb _) hlim (by
    have := hu.comp hφ.tendsto_atTop
    refine this.congr fun k => ?_
    simp [Function.comp, hgb])
  have hSne : S.Nonempty := ⟨x, hS x hx hgx⟩
  have hSbdd : BddAbove S := ⟨B, fun a ha => ha.1.2⟩
  obtain ⟨w, -, hw, hwS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  have hsup : sSup S ∈ Set.Icc (0 : ℝ) B :=
    ⟨(hSne.some_mem.1.1).trans (le_csSup hSbdd hSne.some_mem), csSup_le hSne fun a ha => ha.1.2⟩
  have hwm : (fun k => g (w k)) = fun _ => m := funext fun k =>
    le_antisymm (hle _ (hwS k).1) ((hle x hx).trans (hgx.trans_eq rfl) |>.trans
      ((hwS k).2 x hx) |> fun h => (hgx.trans ((hwS k).2 x hx)))
  have hgs : m ≤ g (sSup S) := husc w _ m (fun k => (hwS k).1) hw (by
    rw [hwm]; exact tendsto_const_nhds)
  exact ⟨hS _ hsup hgs, fun a ha => le_csSup hSbdd ha⟩

lemma plus_bounds {c b : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (1 - c) * (1 - b) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg (by linarith) (by linarith [hb.2]), by nlinarith [hb.1, hb.2]⟩

lemma minus_bounds {c b : ℝ} (hc0 : 0 ≤ c) (hb : b ∈ Set.Icc (0 : ℝ) (1 / (1 + c))) :
    1 - (1 + c) * b ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 := by
  have h := (le_div_iff₀' (by linarith : (0 : ℝ) < 1 + c)).1 hb.2
  exact ⟨⟨by linarith, by nlinarith [hb.1]⟩, hb.1, by nlinarith [hb.1]⟩

lemma argmaxPlus_eq (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) :
    M.argmaxPlus n v = {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ b ∈ Set.Icc (0 : ℝ) 1,
      G M n v ((1 - M.c) * (1 - b), b) ≤ G M n v ((1 - M.c) * (1 - a), a)} := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  ext a
  simp only [Market.argmaxPlus, Set.mem_setOf_eq]
  refine and_congr_right fun ha => forall₂_congr fun b hb => ?_
  rw [Lop_eq_G M hM n hn hγ hv _ _ (plus_bounds hc0 hc1 hb).1 hb.1,
    Lop_eq_G M hM n hn hγ hv _ _ (plus_bounds hc0 hc1 ha).1 ha.1, EReal.coe_le_coe_iff]

lemma argmaxMinus_eq (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) :
    M.argmaxMinus n v = {a | a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)) ∧
      ∀ b ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
      G M n v (1 - (1 + M.c) * b, b) ≤ G M n v (1 - (1 + M.c) * a, a)} := by
  have hc0 := hM.2.1
  ext a
  simp only [Market.argmaxMinus, Set.mem_setOf_eq]
  refine and_congr_right fun ha => forall₂_congr fun b hb => ?_
  rw [Lop_eq_G M hM n hn hγ hv _ _ (minus_bounds hc0 hb).1.1 hb.1,
    Lop_eq_G M hM n hn hγ hv _ _ (minus_bounds hc0 ha).1.1 ha.1, EReal.coe_le_coe_iff]

theorem th_aPlus_greatest (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) :
    IsGreatest (M.argmaxPlus n v) (M.aPlus n v) := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  unfold Market.aPlus
  rw [argmaxPlus_eq M hM n hn hγ hv]
  refine isGreatest_argmax (fun b => G M n v ((1 - M.c) * (1 - b), b)) 1 zero_le_one
    ⟨G M n v (1, 1), ?_⟩ ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact G_mono M hM n hn hγ hv _ _ (plus_bounds hc0 hc1 hb).1 hb.1
      (plus_bounds hc0 hc1 hb).2 hb.2
  · intro b x L hb hbx hL
    have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
      isClosed_Icc.mem_of_tendsto hbx (Filter.Eventually.of_forall hb)
    exact G_usc_seq M hM n hn hγ hv husc (fun k => ((1 - M.c) * (1 - b k), b k))
      ((1 - M.c) * (1 - x), x) (fun k => plus_bounds hc0 hc1 (hb k)) hb
      (plus_bounds hc0 hc1 hx).1 hx.1
      ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hbx)).prodMk_nhds hbx) L hL

theorem th_aMinus_greatest (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) :
    IsGreatest (M.argmaxMinus n v) (M.aMinus n v) := by
  have hc0 := hM.2.1
  unfold Market.aMinus
  rw [argmaxMinus_eq M hM n hn hγ hv]
  refine isGreatest_argmax (fun b => G M n v (1 - (1 + M.c) * b, b)) (1 / (1 + M.c))
    (by positivity) ⟨G M n v (1, 1), ?_⟩ ?_
  · rintro _ ⟨b, hb, rfl⟩
    have h := minus_bounds hc0 hb
    exact G_mono M hM n hn hγ hv _ _ h.1.1 hb.1 h.1.2 h.2.2
  · intro b x L hb hbx hL
    have hx : x ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)) :=
      isClosed_Icc.mem_of_tendsto hbx (Filter.Eventually.of_forall hb)
    exact G_usc_seq M hM n hn hγ hv husc (fun k => (1 - (1 + M.c) * b k, b k))
      (1 - (1 + M.c) * x, x) (fun k => (minus_bounds hc0 (hb k)).1)
      (fun k => (minus_bounds hc0 (hb k)).2) (minus_bounds hc0 hx).1.1 hx.1
      ((tendsto_const_nhds.sub (tendsto_const_nhds.mul hbx)).prodMk_nhds hbx) L hL

/-! ## TH layer 4a: the one-dimensional frontier function `F x a = G (bondAfter x a, a)` -/

noncomputable def F (M : Market Ω) (n : ℕ) (v : ℝ × ℝ → EReal) (x : ℝ × ℝ) (a : ℝ) : ℝ :=
  G M n v (bondAfter M.c x a, a)

lemma bondAfter_le_sell {c : ℝ} (hc0 : 0 ≤ c) (x : ℝ × ℝ) (a : ℝ) :
    bondAfter c x a ≤ x.1 + (1 - c) * (x.2 - a) := by
  unfold bondAfter
  split_ifs with h
  · exact le_rfl
  · nlinarith [mul_nonneg hc0 (by linarith : (0 : ℝ) ≤ a - x.2)]

lemma bondAfter_le_buy {c : ℝ} (hc0 : 0 ≤ c) (x : ℝ × ℝ) (a : ℝ) :
    bondAfter c x a ≤ x.1 + (1 + c) * (x.2 - a) := by
  unfold bondAfter
  split_ifs with h
  · nlinarith [mul_nonneg hc0 (by linarith : (0 : ℝ) ≤ x.2 - a)]
  · exact le_rfl

lemma bondAfter_concave {c : ℝ} (hc0 : 0 ≤ c) (x : ℝ × ℝ) (a a' t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    t * bondAfter c x a + (1 - t) * bondAfter c x a' ≤ bondAfter c x (t * a + (1 - t) * a') := by
  have e1 := mul_le_mul_of_nonneg_left (bondAfter_le_sell hc0 x a) ht0
  have e2 := mul_le_mul_of_nonneg_left (bondAfter_le_sell hc0 x a') (by linarith : (0 : ℝ) ≤ 1 - t)
  have e3 := mul_le_mul_of_nonneg_left (bondAfter_le_buy hc0 x a) ht0
  have e4 := mul_le_mul_of_nonneg_left (bondAfter_le_buy hc0 x a') (by linarith : (0 : ℝ) ≤ 1 - t)
  by_cases h : t * a + (1 - t) * a' ≤ x.2
  · have hb : bondAfter c x (t * a + (1 - t) * a') =
        x.1 + (1 - c) * (x.2 - (t * a + (1 - t) * a')) := if_pos h
    rw [hb]; nlinarith
  · have hb : bondAfter c x (t * a + (1 - t) * a') =
        x.1 + (1 + c) * (x.2 - (t * a + (1 - t) * a')) := if_neg h
    rw [hb]; nlinarith

lemma F_concave (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (a a' : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)))
    (ha' : a' ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c))) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * F M n v x a + (1 - t) * F M n v x a' ≤ F M n v x (t * a + (1 - t) * a') := by
  have hb := th_bondAfter_nonneg M hM x hx a ha
  have hb' := th_bondAfter_nonneg M hM x hx a' ha'
  have h1 := G_concave M hM n hn hγ hv (bondAfter M.c x a, a) (bondAfter M.c x a', a') hb ha.1
    hb' ha'.1 t ht0 ht1
  refine h1.trans (G_mono M hM n hn hγ hv _ (bondAfter M.c x (t * a + (1 - t) * a'),
    t * a + (1 - t) * a') ?_ ?_ (bondAfter_concave hM.2.1 x a a' t ht0 ht1) le_rfl)
  · show 0 ≤ t * bondAfter M.c x a + (1 - t) * bondAfter M.c x a'
    nlinarith [mul_nonneg ht0 hb, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) hb']
  · show 0 ≤ t * a + (1 - t) * a'
    nlinarith [mul_nonneg ht0 ha.1, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) ha'.1]

lemma F_sell_scale (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ)
    (hl : 0 < x.1 / (1 - M.c) + x.2) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hbx : (x.1 / (1 - M.c) + x.2) * b ≤ x.2) :
    F M n v x ((x.1 / (1 - M.c) + x.2) * b) =
      (x.1 / (1 - M.c) + x.2) ^ γ * G M n v ((1 - M.c) * (1 - b), b) := by
  have hc1 := hM.2.2.1
  have hq : x.1 / (1 - M.c) * (1 - M.c) = x.1 := div_mul_cancel₀ _ (by linarith)
  have hbA : bondAfter M.c x ((x.1 / (1 - M.c) + x.2) * b) =
      (x.1 / (1 - M.c) + x.2) * ((1 - M.c) * (1 - b)) := by
    unfold bondAfter
    rw [if_pos hbx]
    linear_combination (-1 : ℝ) * hq
  unfold F
  rw [hbA]
  exact G_hom M hM n hn hv _ hl ((1 - M.c) * (1 - b), b)
    (mul_nonneg (by linarith) (by linarith)) hb0

lemma F_buy_scale (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ)
    (hW : 0 < x.1 + (1 + M.c) * x.2) (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)))
    (hbx : x.2 ≤ (x.1 + (1 + M.c) * x.2) * b) :
    F M n v x ((x.1 + (1 + M.c) * x.2) * b) =
      (x.1 + (1 + M.c) * x.2) ^ γ * G M n v (1 - (1 + M.c) * b, b) := by
  have hbA : bondAfter M.c x ((x.1 + (1 + M.c) * x.2) * b) =
      (x.1 + (1 + M.c) * x.2) * (1 - (1 + M.c) * b) := by
    unfold bondAfter
    split_ifs with h
    · have he : (x.1 + (1 + M.c) * x.2) * b = x.2 := le_antisymm h hbx
      linear_combination (2 * M.c) * he
    · ring
  unfold F
  rw [hbA]
  exact G_hom M hM n hn hv _ hW (1 - (1 + M.c) * b, b) (minus_bounds hM.2.1 hb).1.1 hb.1

/-! ## Layer 4b: the threshold (cone) rule is optimal -/

lemma cc_seg {p y q : ℝ} (hpq : p < q) :
    (q - y) / (q - p) * p + (1 - (q - y) / (q - p)) * q = y := by
  have hne : q - p ≠ 0 := (sub_pos.2 hpq).ne'
  field_simp
  ring

lemma cc_mid (f : ℝ → ℝ) (A : ℝ)
    (hcc : ∀ a ∈ Set.Icc (0 : ℝ) A, ∀ a' ∈ Set.Icc (0 : ℝ) A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * f a + (1 - t) * f a' ≤ f (t * a + (1 - t) * a'))
    {p y q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) A) (hq : q ∈ Set.Icc (0 : ℝ) A) (h1 : p ≤ y)
    (h2 : y ≤ q) : min (f p) (f q) ≤ f y := by
  rcases eq_or_lt_of_le (h1.trans h2) with he | hlt
  · have : y = p := le_antisymm (by rw [he]; exact h2) h1
    rw [this]; exact min_le_left _ _
  · have hqp : 0 < q - p := by linarith
    have ht0 : 0 ≤ (q - y) / (q - p) := div_nonneg (by linarith) hqp.le
    have ht1 : (q - y) / (q - p) ≤ 1 := (div_le_one hqp).2 (by linarith)
    have key := hcc p hp q hq _ ht0 ht1
    rw [cc_seg hlt] at key
    have hm1 := mul_le_mul_of_nonneg_left (min_le_left (f p) (f q)) ht0
    have hm2 := mul_le_mul_of_nonneg_left (min_le_right (f p) (f q))
      (by linarith : (0 : ℝ) ≤ 1 - (q - y) / (q - p))
    linarith

lemma cc_lt_left (f : ℝ → ℝ) (A : ℝ)
    (hcc : ∀ a ∈ Set.Icc (0 : ℝ) A, ∀ a' ∈ Set.Icc (0 : ℝ) A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * f a + (1 - t) * f a' ≤ f (t * a + (1 - t) * a'))
    {p y q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) A) (hq : q ∈ Set.Icc (0 : ℝ) A) (h1 : p < y)
    (h2 : y ≤ q) (hf : f p < f q) : f p < f y := by
  have hlt : p < q := lt_of_lt_of_le h1 h2
  have hqp : 0 < q - p := by linarith
  have ht0 : 0 ≤ (q - y) / (q - p) := div_nonneg (by linarith) hqp.le
  have ht1 : (q - y) / (q - p) < 1 := (div_lt_one hqp).2 (by linarith)
  have key := hcc p hp q hq _ ht0 ht1.le
  rw [cc_seg hlt] at key
  have hm := mul_lt_mul_of_pos_left hf (by linarith : (0 : ℝ) < 1 - (q - y) / (q - p))
  linarith

lemma cc_lt_right (f : ℝ → ℝ) (A : ℝ)
    (hcc : ∀ a ∈ Set.Icc (0 : ℝ) A, ∀ a' ∈ Set.Icc (0 : ℝ) A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * f a + (1 - t) * f a' ≤ f (t * a + (1 - t) * a'))
    {p y q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) A) (hq : q ∈ Set.Icc (0 : ℝ) A) (h1 : p ≤ y)
    (h2 : y < q) (hf : f q < f p) : f q < f y := by
  have hlt : p < q := lt_of_le_of_lt h1 h2
  have hqp : 0 < q - p := by linarith
  have ht0 : 0 < (q - y) / (q - p) := div_pos (by linarith) hqp
  have ht1 : (q - y) / (q - p) ≤ 1 := (div_le_one hqp).2 (by linarith)
  have key := hcc p hp q hq _ ht0.le ht1
  rw [cc_seg hlt] at key
  have hm := mul_lt_mul_of_pos_left hf ht0
  linarith

lemma P_scale (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    {v : ℝ × ℝ → EReal} (hv : IM γ v) (l : ℝ) (hl : 0 < l) (b : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    F M n v (0, l) (l * b) = l ^ γ * G M n v ((1 - M.c) * (1 - b), b) := by
  have h0 : ((0 : ℝ), l).1 / (1 - M.c) + ((0 : ℝ), l).2 = l := by
    show (0 : ℝ) / (1 - M.c) + l = l
    rw [zero_div, zero_add]
  have e := F_sell_scale M hM n hn hv ((0 : ℝ), l) (by rw [h0]; exact hl) b hb.1 hb.2
    (by rw [h0]; show l * b ≤ l; nlinarith [mul_le_mul_of_nonneg_left hb.2 hl.le])
  rw [h0] at e
  exact e

lemma M_scale (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    {v : ℝ × ℝ → EReal} (hv : IM γ v) (W : ℝ) (hW : 0 < W) (b : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c))) :
    F M n v (W, 0) (W * b) = W ^ γ * G M n v (1 - (1 + M.c) * b, b) := by
  have h0 : (W, (0 : ℝ)).1 + (1 + M.c) * (W, (0 : ℝ)).2 = W := by
    show W + (1 + M.c) * 0 = W
    ring
  have e := F_buy_scale M hM n hn hv (W, (0 : ℝ)) (by rw [h0]; exact hW) b hb
    (by rw [h0]; exact mul_nonneg hW.le hb.1)
  rw [h0] at e
  exact e

lemma P_max (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (l : ℝ) (hl : 0 < l) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) l) :
    F M n v (0, l) a ≤ F M n v (0, l) (l * M.aPlus n v) := by
  have hg := (th_aPlus_greatest M hM n hn hγ hv husc).1
  rw [argmaxPlus_eq M hM n hn hγ hv] at hg
  have hl0 : l ≠ 0 := hl.ne'
  have hb : a / l ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ha.1 hl.le, (div_le_one hl).2 ha.2⟩
  have ha' : a = l * (a / l) := by field_simp
  rw [ha', P_scale M hM n hn hv l hl _ hb, P_scale M hM n hn hv l hl _ hg.1]
  exact mul_le_mul_of_nonneg_left (hg.2 _ hb) (Real.rpow_nonneg hl.le γ)

lemma M_max (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (W : ℝ) (hW : 0 < W) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) (W / (1 + M.c))) :
    F M n v (W, 0) a ≤ F M n v (W, 0) (W * M.aMinus n v) := by
  have hg := (th_aMinus_greatest M hM n hn hγ hv husc).1
  rw [argmaxMinus_eq M hM n hn hγ hv] at hg
  have hW0 : W ≠ 0 := hW.ne'
  have hb : a / W ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)) := by
    refine ⟨div_nonneg ha.1 hW.le, ?_⟩
    rw [div_le_iff₀ hW]
    calc a ≤ W / (1 + M.c) := ha.2
      _ = 1 / (1 + M.c) * W := by ring
  have ha' : a = W * (a / W) := by field_simp
  rw [ha', M_scale M hM n hn hv W hW _ hb, M_scale M hM n hn hv W hW _ hg.1]
  exact mul_le_mul_of_nonneg_left (hg.2 _ hb) (Real.rpow_nonneg hW.le γ)

lemma F_eq_P (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (v : ℝ × ℝ → EReal) (x : ℝ × ℝ)
    (hx : x ∈ stateSpace) (l : ℝ) (hl : l = x.1 / (1 - M.c) + x.2) (a : ℝ) (ha : a ≤ x.2) :
    F M n v x a = F M n v (0, l) a := by
  subst hl
  have hc1 := hM.2.2.1
  have hq : x.1 / (1 - M.c) * (1 - M.c) = x.1 := div_mul_cancel₀ _ (by linarith)
  have hx1 : 0 ≤ x.1 / (1 - M.c) := div_nonneg hx.1 (by linarith)
  have e : bondAfter M.c x a = bondAfter M.c (0, x.1 / (1 - M.c) + x.2) a := by
    unfold bondAfter
    dsimp only
    rw [if_pos ha, if_pos (by linarith)]
    linear_combination (-1 : ℝ) * hq
  unfold F
  rw [e]

lemma F_eq_M (M : Market Ω) (n : ℕ) (v : ℝ × ℝ → EReal) (x : ℝ × ℝ)
    (hx : x ∈ stateSpace) (W : ℝ) (hW : W = x.1 + (1 + M.c) * x.2) (a : ℝ) (ha : x.2 ≤ a) :
    F M n v x a = F M n v (W, 0) a := by
  subst hW
  have e : bondAfter M.c x a = bondAfter M.c (x.1 + (1 + M.c) * x.2, 0) a := by
    unfold bondAfter
    dsimp only
    split_ifs with h1 h2 h2
    · have h0 : x.2 = 0 := by linarith [hx.2]
      linear_combination (-2 * M.c) * h0
    · have he : a = x.2 := le_antisymm h1 ha
      linear_combination (2 * M.c) * he
    · exfalso; linarith [hx.2]
    · ring
  unfold F
  rw [e]

lemma sell_iff {c aP : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (haP : aP ∈ Set.Icc (0 : ℝ) 1)
    (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    (if aP < 1 then ENNReal.ofReal (aP / ((1 - c) * (1 - aP))) else ⊤) < ratio x ↔
      (x.1 / (1 - c) + x.2) * aP < x.2 := by
  have h1c : 0 < 1 - c := by linarith
  have hq : x.1 / (1 - c) * (1 - c) = x.1 := div_mul_cancel₀ _ h1c.ne'
  have hx1 : 0 ≤ x.1 / (1 - c) := div_nonneg hx.1 h1c.le
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · have hr : ratio x = ENNReal.ofReal x.2 / 0 := by
      unfold ratio; rw [← h0, ENNReal.ofReal_zero]
    rcases eq_or_lt_of_le hx.2 with h20 | h2pos
    · rw [hr, ← h20, ← h0]
      simp
    · have hne : ENNReal.ofReal x.2 ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h2pos
      rw [hr, ENNReal.div_zero hne, ← h0, zero_div, zero_add]
      split_ifs with h
      · simp only [ENNReal.ofReal_lt_top, true_iff]
        nlinarith [mul_pos h2pos (sub_pos.2 h)]
      · simp only [lt_self_iff_false, false_iff, not_lt]
        nlinarith [mul_le_mul_of_nonneg_left (not_lt.1 h) hx.2]
  · have hr : ratio x = ENNReal.ofReal (x.2 / x.1) := by
      unfold ratio; rw [ENNReal.ofReal_div_of_pos hpos]
    rw [hr]
    split_ifs with h
    · have h1a : 0 < 1 - aP := by linarith
      have hk : 0 ≤ aP / ((1 - c) * (1 - aP)) := div_nonneg haP.1 (mul_nonneg h1c.le h1a.le)
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hk, div_lt_div_iff₀ (mul_pos h1c h1a) hpos]
      have key : (1 - c) * ((x.1 / (1 - c) + x.2) * aP) = aP * x.1 + (1 - c) * x.2 * aP := by
        linear_combination aP * hq
      constructor <;> intro hh <;> nlinarith [key, h1c, hh]
    · simp only [not_top_lt, false_iff, not_lt]
      have : aP = 1 := le_antisymm haP.2 (not_lt.1 h)
      rw [this]
      have : 0 < x.1 / (1 - c) := div_pos hpos h1c
      linarith

lemma buy_le_iff {c aM : ℝ} (hc0 : 0 ≤ c) (haM : aM ∈ Set.Icc (0 : ℝ) (1 / (1 + c)))
    (x : ℝ × ℝ) (hx : x ∈ stateSpace) (hx0 : x ≠ 0) :
    (if aM < 1 / (1 + c) then ENNReal.ofReal (aM / (1 - (1 + c) * aM)) else ⊤) ≤ ratio x ↔
      (x.1 + (1 + c) * x.2) * aM ≤ x.2 := by
  have h1c : 0 < 1 + c := by linarith
  have hb : (1 + c) * aM ≤ 1 := by
    have := mul_le_mul_of_nonneg_left haM.2 h1c.le
    rwa [mul_one_div_cancel h1c.ne'] at this
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · have h2pos : 0 < x.2 := by
      rcases eq_or_lt_of_le hx.2 with h20 | h2pos
      · exact absurd (Prod.ext h0.symm h20.symm) hx0
      · exact h2pos
    have hne : ENNReal.ofReal x.2 ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h2pos
    have hr : ratio x = ⊤ := by
      unfold ratio; rw [← h0, ENNReal.ofReal_zero, ENNReal.div_zero hne]
    rw [hr, ← h0]
    simp only [le_top, true_iff, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hb hx.2]
  · have hr : ratio x = ENNReal.ofReal (x.2 / x.1) := by
      unfold ratio; rw [ENNReal.ofReal_div_of_pos hpos]
    rw [hr]
    split_ifs with h
    · have hd : 0 < 1 - (1 + c) * aM := by
        have := (lt_div_iff₀ h1c).1 h
        linarith
      rw [ENNReal.ofReal_le_ofReal_iff (div_nonneg hx.2 hpos.le), div_le_div_iff₀ hd hpos]
      constructor <;> intro hh <;> linarith
    · simp only [top_le_iff, ENNReal.ofReal_ne_top, false_iff, not_le]
      have hA : aM = 1 / (1 + c) := le_antisymm haM.2 (not_lt.1 h)
      have h1 : (1 + c) * aM = 1 := by rw [hA, mul_one_div_cancel h1c.ne']
      have hpa : 0 < aM := by rw [hA]; positivity
      have e2 : (x.1 + (1 + c) * x.2) * aM = x.1 * aM + x.2 := by linear_combination x.2 * h1
      rw [e2]
      linarith [mul_pos hpos hpa]

lemma sell_val {c aP : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (h0 : 0 ≤ aP) (h1 : aP < 1)
    (x : ℝ × ℝ) :
    (x.1 + (1 - c) * x.2) / (1 + (1 - c) * (ENNReal.ofReal (aP / ((1 - c) * (1 - aP)))).toReal) *
      (ENNReal.ofReal (aP / ((1 - c) * (1 - aP)))).toReal = (x.1 / (1 - c) + x.2) * aP := by
  have hc : (1 - c) ≠ 0 := (by linarith : (0 : ℝ) < 1 - c).ne'
  have ha : (1 - aP) ≠ 0 := (by linarith : (0 : ℝ) < 1 - aP).ne'
  rw [ENNReal.toReal_ofReal (div_nonneg h0 (mul_nonneg (by linarith) (by linarith)))]
  have e : 1 + (1 - c) * (aP / ((1 - c) * (1 - aP))) = 1 / (1 - aP) := by
    field_simp
    ring
  rw [e]
  field_simp

lemma buy_val {c aM : ℝ} (hc0 : 0 ≤ c) (h0 : 0 ≤ aM) (h1 : aM < 1 / (1 + c)) (x : ℝ × ℝ) :
    (x.1 + (1 + c) * x.2) / (1 + (1 + c) * (ENNReal.ofReal (aM / (1 - (1 + c) * aM))).toReal) *
      (ENNReal.ofReal (aM / (1 - (1 + c) * aM))).toReal = (x.1 + (1 + c) * x.2) * aM := by
  have hc : (0 : ℝ) < 1 + c := by linarith
  have hd : 0 < 1 - (1 + c) * aM := by
    have := (lt_div_iff₀ hc).1 h1
    linarith
  have hd' : 1 - (1 + c) * aM ≠ 0 := hd.ne'
  rw [ENNReal.toReal_ofReal (div_nonneg h0 hd.le)]
  have e : 1 + (1 + c) * (aM / (1 - (1 + c) * aM)) = 1 / (1 - (1 + c) * aM) := by
    field_simp
    ring
  rw [e]
  field_simp

lemma cone_cases (qp qm : ENNReal) {c aP aM : ℝ}
    (hqp : qp = if aP < 1 then ENNReal.ofReal (aP / ((1 - c) * (1 - aP))) else ⊤)
    (hqm : qm = if aM < 1 / (1 + c) then ENNReal.ofReal (aM / (1 - (1 + c) * aM)) else ⊤)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (haP : aP ∈ Set.Icc (0 : ℝ) 1)
    (haM : aM ∈ Set.Icc (0 : ℝ) (1 / (1 + c))) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (hx0 : x ≠ 0) :
    ((x.1 / (1 - c) + x.2) * aP < x.2 ∧ coneAmount c qp qm x = (x.1 / (1 - c) + x.2) * aP) ∨
    (x.2 ≤ (x.1 / (1 - c) + x.2) * aP ∧ (x.1 + (1 + c) * x.2) * aM ≤ x.2 ∧
      coneAmount c qp qm x = x.2) ∨
    (x.2 ≤ (x.1 / (1 - c) + x.2) * aP ∧ x.2 < (x.1 + (1 + c) * x.2) * aM ∧
      coneAmount c qp qm x = (x.1 + (1 + c) * x.2) * aM) := by
  have hs := sell_iff hc0 hc1 haP x hx
  have hb := buy_le_iff hc0 haM x hx hx0
  rw [← hqp] at hs
  rw [← hqm] at hb
  by_cases h1 : qp < ratio x
  · left
    refine ⟨hs.1 h1, ?_⟩
    have haP1 : aP < 1 := by
      by_contra h
      rw [hqp, if_neg h] at h1
      exact not_top_lt h1
    unfold coneAmount
    rw [if_pos h1, hqp, if_pos haP1]
    exact sell_val hc0 hc1 haP.1 haP1 x
  · by_cases h2 : qm ≤ ratio x
    · right; left
      refine ⟨not_lt.1 (mt hs.2 h1), hb.1 h2, ?_⟩
      unfold coneAmount
      rw [if_neg h1, if_pos h2]
    · right; right
      refine ⟨not_lt.1 (mt hs.2 h1), not_le.1 (mt hb.2 h2), ?_⟩
      unfold coneAmount
      rw [if_neg h1, if_neg h2]
      by_cases hA : aM < 1 / (1 + c)
      · have hne : qm ≠ ⊤ := by rw [hqm, if_pos hA]; exact ENNReal.ofReal_ne_top
        rw [if_neg hne, hqm, if_pos hA]
        exact buy_val hc0 haM.1 hA x
      · have he : qm = ⊤ := by rw [hqm, if_neg hA]
        rw [if_pos he]
        have : aM = 1 / (1 + c) := le_antisymm haM.2 (not_lt.1 hA)
        rw [this, mul_one_div]

lemma Ps (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace) (l : ℝ)
    (hl : l = x.1 / (1 - M.c) + x.2) (hlpos : 0 < l) (hp : x.2 ≤ l * M.aPlus n v) (a : ℝ)
    (ha0 : 0 ≤ a) (ha2 : a ≤ x.2) : F M n v x a ≤ F M n v x x.2 := by
  have haP := (th_aPlus_greatest M hM n hn hγ hv husc).1.1
  have hx1 : 0 ≤ x.1 / (1 - M.c) := div_nonneg hx.1 (by linarith [hM.2.2.1])
  have hx2l : x.2 ≤ l := by rw [hl]; linarith
  have hpl : l * M.aPlus n v ≤ l := by
    nlinarith [mul_le_mul_of_nonneg_left haP.2 hlpos.le]
  rw [F_eq_P M hM n v x hx l hl a ha2, F_eq_P M hM n v x hx l hl x.2 le_rfl]
  have hccP : ∀ b ∈ Set.Icc (0 : ℝ) l, ∀ b' ∈ Set.Icc (0 : ℝ) l, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * F M n v (0, l) b + (1 - t) * F M n v (0, l) b' ≤
        F M n v (0, l) (t * b + (1 - t) * b') := by
    intro b hb b' hb' t ht0 ht1
    exact F_concave M hM n hn hγ hv (0, l) ⟨le_rfl, hlpos.le⟩ b b' (by simpa using hb)
      (by simpa using hb') t ht0 ht1
  have hm := cc_mid (F M n v (0, l)) l hccP (p := a) (y := x.2) (q := l * M.aPlus n v)
    ⟨ha0, by linarith⟩ ⟨mul_nonneg hlpos.le haP.1, hpl⟩ ha2 hp
  rw [min_eq_left (P_max M hM n hn hγ hv husc l hlpos a ⟨ha0, by linarith⟩)] at hm
  exact hm

lemma Ms (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace) (W : ℝ)
    (hW : W = x.1 + (1 + M.c) * x.2) (hWpos : 0 < W) (hq : W * M.aMinus n v ≤ x.2) (a : ℝ)
    (ha2 : x.2 ≤ a) (haA : a ≤ x.2 + x.1 / (1 + M.c)) : F M n v x a ≤ F M n v x x.2 := by
  have haM := (th_aMinus_greatest M hM n hn hγ hv husc).1.1
  have hc0 := hM.2.1
  have hAW : x.2 + x.1 / (1 + M.c) = W / (1 + M.c) := by
    have : (1 + M.c) ≠ 0 := (by linarith : (0 : ℝ) < 1 + M.c).ne'
    rw [hW]; field_simp; ring
  rw [hAW] at haA
  have hqW : W * M.aMinus n v ≤ W / (1 + M.c) :=
    (mul_le_mul_of_nonneg_left haM.2 hWpos.le).trans_eq (mul_one_div _ _)
  rw [F_eq_M M n v x hx W hW a ha2, F_eq_M M n v x hx W hW x.2 le_rfl]
  have hccM : ∀ b ∈ Set.Icc (0 : ℝ) (W / (1 + M.c)), ∀ b' ∈ Set.Icc (0 : ℝ) (W / (1 + M.c)),
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * F M n v (W, 0) b + (1 - t) * F M n v (W, 0) b' ≤
        F M n v (W, 0) (t * b + (1 - t) * b') := by
    intro b hb b' hb' t ht0 ht1
    exact F_concave M hM n hn hγ hv (W, 0) ⟨hWpos.le, le_rfl⟩ b b' (by simpa using hb)
      (by simpa using hb') t ht0 ht1
  have hm := cc_mid (F M n v (W, 0)) (W / (1 + M.c)) hccM (p := W * M.aMinus n v) (y := x.2)
    (q := a) ⟨mul_nonneg hWpos.le haM.1, hqW⟩ ⟨by linarith [hx.2], haA⟩ hq ha2
  rw [min_eq_right (M_max M hM n hn hγ hv husc W hWpos a ⟨by linarith [hx.2], haA⟩)] at hm
  exact hm

lemma hccx_of (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    ∀ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
      ∀ a' ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * F M n v x a + (1 - t) * F M n v x a' ≤ F M n v x (t * a + (1 - t) * a') :=
  fun a ha a' ha' t ht0 ht1 => F_concave M hM n hn hγ hv x hx a a' ha ha' t ht0 ht1

lemma no_gap (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace) (l W : ℝ)
    (hl : l = x.1 / (1 - M.c) + x.2) (hW : W = x.1 + (1 + M.c) * x.2)
    (h1 : l * M.aPlus n v < x.2) (h2 : x.2 < W * M.aMinus n v) : False := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  have hgP := th_aPlus_greatest M hM n hn hγ hv husc
  have haP := hgP.1.1
  have haM := (th_aMinus_greatest M hM n hn hγ hv husc).1.1
  have hx1 : 0 ≤ x.1 / (1 - M.c) := div_nonneg hx.1 (by linarith)
  have hl0 : 0 ≤ l := by rw [hl]; linarith [hx.2]
  have hx2pos : 0 < x.2 := lt_of_le_of_lt (mul_nonneg hl0 haP.1) h1
  have hlpos : 0 < l := by rw [hl]; linarith
  have hWpos : 0 < W := by
    rw [hW]; nlinarith [hx.1, mul_pos (show (0 : ℝ) < 1 + M.c by linarith) hx2pos]
  have hAW : x.2 + x.1 / (1 + M.c) = W / (1 + M.c) := by
    have : (1 + M.c) ≠ 0 := (by linarith : (0 : ℝ) < 1 + M.c).ne'
    rw [hW]; field_simp; ring
  have hqW : W * M.aMinus n v ≤ W / (1 + M.c) :=
    (mul_le_mul_of_nonneg_left haM.2 hWpos.le).trans_eq (mul_one_div _ _)
  have hx2A : x.2 ≤ x.2 + x.1 / (1 + M.c) := by
    have : 0 ≤ x.1 / (1 + M.c) := div_nonneg hx.1 (by linarith)
    linarith
  have hpA : l * M.aPlus n v ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)) :=
    ⟨mul_nonneg hlpos.le haP.1, by linarith⟩
  have hqA : W * M.aMinus n v ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)) :=
    ⟨mul_nonneg hWpos.le haM.1, by rw [hAW]; exact hqW⟩
  have hccx := hccx_of M hM n hn hγ hv x hx
  by_cases hfo : F M n v x (l * M.aPlus n v) ≤ F M n v x (W * M.aMinus n v)
  · have hm := cc_mid (F M n v x) _ hccx hpA hqA h1.le h2.le
    rw [min_eq_left hfo] at hm
    have eP : F M n v x (l * M.aPlus n v) = F M n v (0, l) (l * M.aPlus n v) :=
      F_eq_P M hM n v x hx l hl _ h1.le
    have eX : F M n v x x.2 = F M n v (0, l) x.2 := F_eq_P M hM n v x hx l hl _ le_rfl
    have hl0' : l ≠ 0 := hlpos.ne'
    have hb2 : x.2 / l ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx.2 hlpos.le, (div_le_one hlpos).2 (by rw [hl]; linarith)⟩
    have hlx : l * (x.2 / l) = x.2 := by field_simp
    have hmem : x.2 / l ∈ M.argmaxPlus n v := by
      rw [argmaxPlus_eq M hM n hn hγ hv]
      refine ⟨hb2, fun b hb => ?_⟩
      have e1 := P_scale M hM n hn hv l hlpos b hb
      have e2 := P_scale M hM n hn hv l hlpos _ hb2
      rw [hlx] at e2
      have hle1 := P_max M hM n hn hγ hv husc l hlpos (l * b)
        ⟨mul_nonneg hlpos.le hb.1, by nlinarith [mul_le_mul_of_nonneg_left hb.2 hlpos.le]⟩
      have key : l ^ γ * G M n v ((1 - M.c) * (1 - b), b) ≤
          l ^ γ * G M n v ((1 - M.c) * (1 - x.2 / l), x.2 / l) := by
        rw [← e1, ← e2]; linarith
      exact le_of_mul_le_mul_left key (Real.rpow_pos_of_pos hlpos γ)
    have h3 := hgP.2 hmem
    have h4 := mul_le_mul_of_nonneg_left h3 hlpos.le
    rw [hlx] at h4
    linarith
  · push_neg at hfo
    have hm := cc_lt_right (F M n v x) _ hccx hpA hqA h1.le h2 hfo
    have eQ : F M n v x (W * M.aMinus n v) = F M n v (W, 0) (W * M.aMinus n v) :=
      F_eq_M M n v x hx W hW _ h2.le
    have eX : F M n v x x.2 = F M n v (W, 0) x.2 := F_eq_M M n v x hx W hW _ le_rfl
    have hle := M_max M hM n hn hγ hv husc W hWpos x.2 ⟨hx.2, by rw [← hAW]; exact hx2A⟩
    linarith

theorem th_q_le (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) : M.qMinus n v ≤ M.qPlus n v := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  have haP := (th_aPlus_greatest M hM n hn hγ hv husc).1.1
  have haM := (th_aMinus_greatest M hM n hn hγ hv husc).1.1
  by_contra hcon
  push_neg at hcon
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hcon
  have hx : ((1 : ℝ), r) ∈ stateSpace := ⟨zero_le_one, hr0⟩
  have hx0 : ((1 : ℝ), r) ≠ 0 := by
    intro h
    have := congrArg Prod.fst h
    simp at this
  have hrat : ratio ((1 : ℝ), r) = ENNReal.ofReal r := by
    unfold ratio; simp
  have hs := sell_iff hc0 hc1 haP ((1 : ℝ), r) hx
  have hb := buy_le_iff hc0 haM ((1 : ℝ), r) hx hx0
  have h1 : M.qPlus n v < ratio ((1 : ℝ), r) := by rw [hrat]; exact hr1
  have h2 : ¬ M.qMinus n v ≤ ratio ((1 : ℝ), r) := by rw [hrat]; exact not_le.2 hr2
  exact no_gap M hM n hn hγ hv husc _ hx _ _ rfl rfl (hs.1 h1) (not_le.1 (mt hb.2 h2))

theorem rule_opt (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    coneAmount M.c (M.qPlus n v) (M.qMinus n v) x ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)) ∧
    ∀ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
      F M n v x a ≤ F M n v x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x) := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  have haP := (th_aPlus_greatest M hM n hn hγ hv husc).1.1
  have haM := (th_aMinus_greatest M hM n hn hγ hv husc).1.1
  by_cases hx0 : x = 0
  · subst hx0
    have hcone : coneAmount M.c (M.qPlus n v) (M.qMinus n v) 0 = 0 := by
      unfold coneAmount; simp
    rw [hcone]
    simp only [Prod.fst_zero, Prod.snd_zero, zero_div, add_zero]
    refine ⟨⟨le_rfl, le_rfl⟩, fun a ha => ?_⟩
    rw [le_antisymm ha.2 ha.1]
  · have hcases := cone_cases (M.qPlus n v) (M.qMinus n v) rfl rfl hc0 hc1 haP haM x hx hx0
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = x.1 / (1 - M.c) + x.2 := ⟨_, rfl⟩
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = x.1 + (1 + M.c) * x.2 := ⟨_, rfl⟩
    rw [← hl, ← hW] at hcases
    have hx1 : 0 ≤ x.1 / (1 - M.c) := div_nonneg hx.1 (by linarith)
    have hpos : 0 < x.1 ∨ 0 < x.2 := by
      by_contra h
      push_neg at h
      exact hx0 (Prod.ext (le_antisymm h.1 hx.1) (le_antisymm h.2 hx.2))
    have hlpos : 0 < l := by
      rw [hl]
      rcases hpos with h | h
      · have : 0 < x.1 / (1 - M.c) := div_pos h (by linarith)
        linarith [hx.2]
      · linarith
    have hWpos : 0 < W := by
      rw [hW]
      rcases hpos with h | h
      · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 + M.c by linarith) hx.2]
      · nlinarith [mul_pos (show (0 : ℝ) < 1 + M.c by linarith) h, hx.1]
    have hAW : x.2 + x.1 / (1 + M.c) = W / (1 + M.c) := by
      have : (1 + M.c) ≠ 0 := (by linarith : (0 : ℝ) < 1 + M.c).ne'
      rw [hW]; field_simp; ring
    have hx2A : x.2 ≤ x.2 + x.1 / (1 + M.c) := by
      have : 0 ≤ x.1 / (1 + M.c) := div_nonneg hx.1 (by linarith)
      linarith
    have hccx := hccx_of M hM n hn hγ hv x hx
    rcases hcases with ⟨hlt, hval⟩ | ⟨hle1, hle2, hval⟩ | ⟨hle1, hlt2, hval⟩
    · rw [hval]
      have hpA : l * M.aPlus n v ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)) :=
        ⟨mul_nonneg hlpos.le haP.1, by linarith⟩
      have low : ∀ a, 0 ≤ a → a ≤ x.2 → F M n v x a ≤ F M n v x (l * M.aPlus n v) := by
        intro a ha0 ha2
        rw [F_eq_P M hM n v x hx l hl a ha2, F_eq_P M hM n v x hx l hl _ hlt.le]
        exact P_max M hM n hn hγ hv husc l hlpos a ⟨ha0, by rw [hl]; linarith⟩
      refine ⟨hpA, fun a ha => ?_⟩
      by_cases ha2 : a ≤ x.2
      · exact low a ha.1 ha2
      · by_contra hcon
        push_neg at hcon
        have := cc_lt_left (F M n v x) _ hccx hpA ha hlt (le_of_lt (not_le.1 ha2)) hcon
        linarith [low x.2 hx.2 le_rfl]
    · rw [hval]
      refine ⟨⟨hx.2, hx2A⟩, fun a ha => ?_⟩
      rcases le_total a x.2 with ha2 | ha2
      · exact Ps M hM n hn hγ hv husc x hx l hl hlpos hle1 a ha.1 ha2
      · exact Ms M hM n hn hγ hv husc x hx W hW hWpos hle2 a ha2 ha.2
    · rw [hval]
      have hqW : W * M.aMinus n v ≤ W / (1 + M.c) :=
        (mul_le_mul_of_nonneg_left haM.2 hWpos.le).trans_eq (mul_one_div _ _)
      have hqA : W * M.aMinus n v ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)) :=
        ⟨mul_nonneg hWpos.le haM.1, by rw [hAW]; exact hqW⟩
      have up : ∀ a, x.2 ≤ a → a ≤ x.2 + x.1 / (1 + M.c) →
          F M n v x a ≤ F M n v x (W * M.aMinus n v) := by
        intro a ha2 haA
        rw [F_eq_M M n v x hx W hW a ha2, F_eq_M M n v x hx W hW _ hlt2.le]
        exact M_max M hM n hn hγ hv husc W hWpos a ⟨by linarith [hx.2], by rw [← hAW]; exact haA⟩
      refine ⟨hqA, fun a ha => ?_⟩
      rcases le_total a x.2 with ha2 | ha2
      · exact (Ps M hM n hn hγ hv husc x hx l hl hlpos hle1 a ha.1 ha2).trans
          (up x.2 le_rfl hx2A)
      · exact up a ha2 ha.2

lemma ratio_measurable : Measurable ratio := by
  unfold ratio
  fun_prop

lemma cone_measurable (c : ℝ) (qp qm : ENNReal) : Measurable (coneAmount c qp qm) := by
  have hr := ratio_measurable
  unfold coneAmount
  exact Measurable.ite (measurableSet_lt measurable_const hr) (by fun_prop)
    (Measurable.ite (measurableSet_le measurable_const hr) measurable_snd
      (Measurable.ite (MeasurableSet.const _) (by fun_prop) (by fun_prop)))

theorem th_rule_dec (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) :
    IsDecisionRule M.c (fun x => (bondAfter M.c x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x),
        coneAmount M.c (M.qPlus n v) (M.qMinus n v) x)) := by
  refine ⟨?_, fun x hx => th_frontier_adm M hM x hx _ (rule_opt M hM n hn hγ hv husc x hx).1⟩
  have hcone := cone_measurable M.c (M.qPlus n v) (M.qMinus n v)
  have hb : Measurable (fun x : ℝ × ℝ =>
      bondAfter M.c x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x)) := by
    unfold bondAfter
    exact Measurable.ite (measurableSet_le hcone measurable_snd) (by fun_prop) (by fun_prop)
  exact hb.prodMk hcone

theorem childTH_holds : ∀ {Ω : Type u} [MeasurableSpace Ω] (M : Market Ω), M.Assumptions →
    ∀ n < M.N, ∀ v : ℝ × ℝ → EReal, IM M.γ v → UpperSemicontinuousOn v stateSpace →
      IsGreatest (M.argmaxPlus n v) (M.aPlus n v) ∧
      IsGreatest (M.argmaxMinus n v) (M.aMinus n v) ∧
      M.qMinus n v ≤ M.qPlus n v ∧
      IsDecisionRule M.c (fun x => (bondAfter M.c x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x),
        coneAmount M.c (M.qPlus n v) (M.qMinus n v) x)) ∧
      ∀ x ∈ stateSpace,
        M.Lop n v x (bondAfter M.c x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x),
          coneAmount M.c (M.qPlus n v) (M.qMinus n v) x) = M.Top n v x ∧
        M.Top n v x = ⨆ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
          M.Lop n v x (bondAfter M.c x a, a) := by
  intro Ω _ M hM n hn v hv husc
  have hγ := th_gamma_ne_zero M hM
  refine ⟨th_aPlus_greatest M hM n hn hγ hv husc, th_aMinus_greatest M hM n hn hγ hv husc,
    th_q_le M hM n hn hγ hv husc, th_rule_dec M hM n hn hγ hv husc, fun x hx => ?_⟩
  have hTop := Top_frontier M hM n hn hγ hv x hx
  obtain ⟨hmem, hopt⟩ := rule_opt M hM n hn hγ hv husc x hx
  have hL : ∀ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
      M.Lop n v x (bondAfter M.c x a, a) = ((F M n v x a : ℝ) : EReal) :=
    fun a ha => Lop_eq_G M hM n hn hγ hv x _ (th_bondAfter_nonneg M hM x hx a ha) ha.1
  have hS : (⨆ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
      M.Lop n v x (bondAfter M.c x a, a)) =
      M.Lop n v x (bondAfter M.c x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x),
        coneAmount M.c (M.qPlus n v) (M.qMinus n v) x) := by
    apply le_antisymm
    · refine iSup₂_le fun a ha => ?_
      rw [hL a ha, hL _ hmem]
      exact EReal.coe_le_coe_iff.2 (hopt a ha)
    · exact le_iSup₂_of_le (f := fun a (_ : a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c))) =>
        M.Lop n v x (bondAfter M.c x a, a)) _ hmem le_rfl
  exact ⟨by rw [hTop, hS], hTop⟩

/-! ## P452 pieces (proposition_4_5_2, a41ba4b5): well-definedness and cone-rule maximizer -/

theorem th_cone_rule (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) :
    IsConeRule (coneAmount M.c (M.qPlus n v) (M.qMinus n v)) := by
  have hc0 := hM.2.1
  have hc1 := hM.2.2.1
  have haP := (th_aPlus_greatest M hM n hn hγ hv husc).1.1
  have haM := (th_aMinus_greatest M hM n hn hγ hv husc).1.1
  have hq := th_q_le M hM n hn hγ hv husc
  refine ⟨fun x hx => (rule_opt M hM n hn hγ hv husc x hx).1.1, M.qMinus n v, M.qPlus n v, hq,
    fun x => (x.1 / (1 - M.c) + x.2) * M.aPlus n v,
    fun x => (x.1 + (1 + M.c) * x.2) * M.aMinus n v, by fun_prop, by fun_prop,
    fun x hx => ⟨?_, ?_⟩, fun x hx hx0 => ?_⟩
  · exact mul_nonneg (add_nonneg (div_nonneg hx.1 (by linarith)) hx.2) haP.1
  · exact mul_nonneg (by nlinarith [hx.1, hx.2]) haM.1
  · have hs := sell_iff hc0 hc1 haP x hx
    have hb := buy_le_iff hc0 haM x hx hx0
    have hc := cone_cases (M.qPlus n v) (M.qMinus n v) rfl rfl hc0 hc1 haP haM x hx hx0
    refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_⟩
    · have hp := hs.1 h
      rcases hc with ⟨_, h2⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _⟩
      · exact ⟨h2, hp⟩
      · exact absurd hp (not_lt.2 h1)
      · exact absurd hp (not_lt.2 h1)
    · have hp : ¬ (x.1 / (1 - M.c) + x.2) * M.aPlus n v < x.2 :=
        fun hh => absurd (hs.2 hh) (not_lt.2 h')
      have hq' := hb.1 h
      rcases hc with ⟨h1, _⟩ | ⟨_, _, h3⟩ | ⟨_, h2, _⟩
      · exact absurd h1 hp
      · exact h3
      · exact absurd hq' (not_le.2 h2)
    · have hq' : ¬ (x.1 + (1 + M.c) * x.2) * M.aMinus n v ≤ x.2 :=
        fun hh => absurd (hb.2 hh) (not_le.2 h)
      have hp : ¬ (x.1 / (1 - M.c) + x.2) * M.aPlus n v < x.2 :=
        fun hh => absurd (hs.2 hh) (not_lt.2 (h.le.trans hq))
      rcases hc with ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, h2, h3⟩
      · exact absurd h1 hp
      · exact absurd h2 hq'
      · exact ⟨h3, h2⟩

theorem th_wd (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v) (x : ℝ × ℝ) (a : ℝ × ℝ)
    (ha : a ∈ admissibleSet M.c x) :
    (∫⁻ ω, (v (M.transition n a (M.R (n + 1) ω))).toENNReal ∂M.P) < ⊤ ∨
      (∫⁻ ω, (-v (M.transition n a (M.R (n + 1) ω))).toENNReal ∂M.P) < ⊤ := by
  left
  have hI := th_integrable M hM n hn hγ hv a ha.1 ha.2.1
  have h : ∀ ω, (v (M.transition n a (M.R (n + 1) ω))).toENNReal =
      ENNReal.ofReal (vr v (M.transition n a (M.R (n + 1) ω))) := by
    intro ω
    have hne := th_IM_ne_top hv _ (th_transition_mem M hM n hn a ha.1 ha.2.1 ω)
    first
    | (rw [EReal.toENNReal_of_ne_top hne]; rfl)
    | (unfold EReal.toENNReal; rw [if_neg hne]; rfl)
  simp_rw [h]
  exact hI.lintegral_lt_top

/-! ## P452 (i): the terminal reward `U(x₀ + x₁)` is in `IM` and usc -/

lemma lin_bound (f : ℝ × ℝ → ℝ)
    (hmono : ∀ x ∈ stateSpace, ∀ y ∈ stateSpace, x.1 ≤ y.1 → x.2 ≤ y.2 → f x ≤ f y)
    (hconc : ∀ x ∈ stateSpace, ∀ y ∈ stateSpace, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * f x + (1 - t) * f y ≤ f (t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ stateSpace, f x ≤ C * (1 + x.1 + x.2) := by
  refine ⟨|f (1, 1)| + |f (0, 0)|, by positivity, fun x hx => ?_⟩
  have hx1 := hx.1
  have hx2 := hx.2
  have hspos : 0 < 1 + x.1 + x.2 := by linarith
  have ht0 : 0 ≤ 1 / (1 + x.1 + x.2) := by positivity
  have ht1 : 1 / (1 + x.1 + x.2) ≤ 1 := by rw [div_le_one hspos]; linarith
  have h := hconc x hx (0, 0) th_zero_mem _ ht0 ht1
  simp only [mul_zero, add_zero] at h
  have hq1 : 1 / (1 + x.1 + x.2) * x.1 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hspos]; linarith
  have hq2 : 1 / (1 + x.1 + x.2) * x.2 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hspos]; linarith
  have hm := hmono (1 / (1 + x.1 + x.2) * x.1, 1 / (1 + x.1 + x.2) * x.2)
    ⟨mul_nonneg ht0 hx1, mul_nonneg ht0 hx2⟩ (1, 1) ⟨zero_le_one, zero_le_one⟩ hq1 hq2
  have hk : 1 / (1 + x.1 + x.2) * f x ≤ |f (1, 1)| + |f (0, 0)| := by
    have e1 := le_abs_self (f (1, 1))
    have e2 := neg_abs_le (f (0, 0))
    have e3 := mul_nonneg (sub_nonneg.2 ht1) (by linarith : 0 ≤ f (0, 0) + |f (0, 0)|)
    have e4 := mul_nonneg ht0 (abs_nonneg (f (0, 0)))
    nlinarith
  have he : f x = (1 + x.1 + x.2) * (1 / (1 + x.1 + x.2) * f x) := by
    field_simp
  rw [he, mul_comm (|f (1, 1)| + |f (0, 0)|)]
  exact mul_le_mul_of_nonneg_left hk hspos.le

theorem p452_terminal (M : Market Ω) (hM : M.Assumptions) :
    IM M.γ (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) ∧
      UpperSemicontinuousOn (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) stateSpace := by
  obtain ⟨_, _, _, _, _, _, _, hmono, hconc, hcont, hhom⟩ := hM
  have hsum : Set.MapsTo (fun x : ℝ × ℝ => x.1 + x.2) stateSpace (Set.Ici 0) :=
    fun x hx => add_nonneg hx.1 hx.2
  have hcU : ContinuousOn (fun x : ℝ × ℝ => M.U (x.1 + x.2)) stateSpace :=
    hcont.comp (by fun_prop) hsum
  have husc : UpperSemicontinuousOn (fun x => ((M.U (x.1 + x.2) : ℝ) : EReal)) stateSpace :=
    (continuous_coe_real_ereal.comp_continuousOn hcU).upperSemicontinuousOn
  have hinc : ∀ x ∈ stateSpace, ∀ y ∈ stateSpace, x.1 ≤ y.1 → x.2 ≤ y.2 →
      M.U (x.1 + x.2) ≤ M.U (y.1 + y.2) := fun x hx y hy h1 h2 =>
    hmono.monotoneOn (hsum hx) (hsum hy) (by linarith)
  have hcc : ∀ x ∈ stateSpace, ∀ y ∈ stateSpace, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * M.U (x.1 + x.2) + (1 - t) * M.U (y.1 + y.2) ≤
        M.U ((t * x.1 + (1 - t) * y.1) + (t * x.2 + (1 - t) * y.2)) := by
    intro x hx y hy t ht0 ht1
    have h := hconc.concaveOn.2 (hsum hx) (hsum hy) ht0 (sub_nonneg.2 ht1) (by ring)
    simp only [smul_eq_mul] at h
    exact h.trans_eq (by congr 1; ring)
  obtain ⟨C, hC0, hC⟩ := lin_bound (fun x => M.U (x.1 + x.2)) hinc hcc
  refine ⟨⟨(upperSemicontinuousOn_iff_restrict.2 husc).measurable, fun x _ => EReal.coe_ne_bot _,
    ⟨C, hC0, fun x hx => EReal.coe_le_coe_iff.2 (hC x hx)⟩,
    fun x hx y hy h1 h2 => EReal.coe_le_coe_iff.2 (hinc x hx y hy h1 h2), ?_, ?_⟩, husc⟩
  · intro x hx y hy t ht0 ht1
    show (t : EReal) * ((M.U (x.1 + x.2) : ℝ) : EReal) + ((1 - t : ℝ) : EReal) *
        ((M.U (y.1 + y.2) : ℝ) : EReal) ≤
      ((M.U ((t * x.1 + (1 - t) * y.1) + (t * x.2 + (1 - t) * y.2)) : ℝ) : EReal)
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (hcc x hx y hy t ht0 ht1)
  · intro lam hl x hx
    show ((M.U (lam * x.1 + lam * x.2) : ℝ) : EReal) =
      ((lam ^ M.γ : ℝ) : EReal) * ((M.U (x.1 + x.2) : ℝ) : EReal)
    rw [← EReal.coe_mul, show lam * x.1 + lam * x.2 = lam * (x.1 + x.2) by ring,
      hhom lam hl _ (hsum hx)]

/-! ## P452 (ii): `Top` preserves `IM` and usc -/

lemma adm_zero {c : ℝ} (hc1 : c < 1) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    ((0 : ℝ), (0 : ℝ)) ∈ admissibleSet c x := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  show (0 : ℝ) + 0 ≤ x.1 + x.2 - c * |0 - x.2|
  rw [zero_sub, abs_neg, abs_of_nonneg hx.2]
  nlinarith [hx.1, mul_nonneg (sub_nonneg.2 hc1.le) hx.2]

lemma adm_mono {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (x y : ℝ × ℝ) (h1 : x.1 ≤ y.1)
    (h2 : x.2 ≤ y.2) (a : ℝ × ℝ) (ha : a ∈ admissibleSet c x) : a ∈ admissibleSet c y := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  refine ⟨ha1, ha2, ?_⟩
  have ha3' : a.1 + a.2 ≤ x.1 + x.2 - c * |a.2 - x.2| := ha3
  show a.1 + a.2 ≤ y.1 + y.2 - c * |a.2 - y.2|
  have hab : |a.2 - y.2| ≤ |a.2 - x.2| + (y.2 - x.2) := by
    have := abs_sub_le a.2 x.2 y.2
    rwa [abs_of_nonpos (by linarith : x.2 - y.2 ≤ 0), neg_sub] at this
  have := mul_le_mul_of_nonneg_left hab hc0
  nlinarith [mul_le_mul_of_nonneg_right hc1.le (sub_nonneg.2 h2)]

lemma adm_scale {c : ℝ} (x : ℝ × ℝ) (l : ℝ) (hl : 0 < l) (a : ℝ × ℝ)
    (ha : a ∈ admissibleSet c x) :
    ((l * a.1, l * a.2) : ℝ × ℝ) ∈ admissibleSet c (l * x.1, l * x.2) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have ha3' : a.1 + a.2 ≤ x.1 + x.2 - c * |a.2 - x.2| := ha3
  refine ⟨mul_nonneg hl.le ha1, mul_nonneg hl.le ha2, ?_⟩
  show l * a.1 + l * a.2 ≤ l * x.1 + l * x.2 - c * |l * a.2 - l * x.2|
  rw [← mul_sub, abs_mul, abs_of_pos hl]
  nlinarith [mul_le_mul_of_nonneg_left ha3' hl.le]

lemma adm_convex {c : ℝ} (hc0 : 0 ≤ c) (x y a b : ℝ × ℝ) (ha : a ∈ admissibleSet c x)
    (hb : b ∈ admissibleSet c y) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t * a.1 + (1 - t) * b.1, t * a.2 + (1 - t) * b.2) : ℝ × ℝ) ∈
      admissibleSet c (t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have ha3' : a.1 + a.2 ≤ x.1 + x.2 - c * |a.2 - x.2| := ha3
  have hb3' : b.1 + b.2 ≤ y.1 + y.2 - c * |b.2 - y.2| := hb3
  have hs : 0 ≤ 1 - t := sub_nonneg.2 ht1
  refine ⟨add_nonneg (mul_nonneg ht0 ha1) (mul_nonneg hs hb1),
    add_nonneg (mul_nonneg ht0 ha2) (mul_nonneg hs hb2), ?_⟩
  show t * a.1 + (1 - t) * b.1 + (t * a.2 + (1 - t) * b.2) ≤
    t * x.1 + (1 - t) * y.1 + (t * x.2 + (1 - t) * y.2) -
      c * |t * a.2 + (1 - t) * b.2 - (t * x.2 + (1 - t) * y.2)|
  have habs : |t * a.2 + (1 - t) * b.2 - (t * x.2 + (1 - t) * y.2)| ≤
      t * |a.2 - x.2| + (1 - t) * |b.2 - y.2| := by
    have h := abs_add_le (t * (a.2 - x.2)) ((1 - t) * (b.2 - y.2))
    rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hs] at h
    calc _ = |t * (a.2 - x.2) + (1 - t) * (b.2 - y.2)| := by congr 1; ring
      _ ≤ _ := h
  nlinarith [mul_le_mul_of_nonneg_left ha3' ht0, mul_le_mul_of_nonneg_left hb3' hs,
    mul_le_mul_of_nonneg_left habs hc0]

/-- The optimal value, as a real number: `F` at the cone rule. -/
noncomputable def T (M : Market Ω) (n : ℕ) (v : ℝ × ℝ → EReal) (x : ℝ × ℝ) : ℝ :=
  F M n v x (coneAmount M.c (M.qPlus n v) (M.qMinus n v) x)

lemma Top_eq_T (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    M.Top n v x = ((T M n v x : ℝ) : EReal) := by
  have hTop := Top_frontier M hM n hn hγ hv x hx
  obtain ⟨hmem, hopt⟩ := rule_opt M hM n hn hγ hv husc x hx
  have hL : ∀ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
      M.Lop n v x (bondAfter M.c x a, a) = ((F M n v x a : ℝ) : EReal) :=
    fun a ha => Lop_eq_G M hM n hn hγ hv x _ (th_bondAfter_nonneg M hM x hx a ha) ha.1
  rw [hTop]
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    rw [hL a ha]
    exact EReal.coe_le_coe_iff.2 (hopt a ha)
  · have h := hL _ hmem
    unfold T
    rw [← h]
    exact le_iSup₂_of_le (f := fun a (_ : a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c))) =>
        M.Lop n v x (bondAfter M.c x a, a)) _ hmem le_rfl

lemma G_le_T (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (a : ℝ × ℝ) (ha : a ∈ admissibleSet M.c x) : G M n v a ≤ T M n v x := by
  have h : M.Lop n v x a ≤ M.Top n v x :=
    le_iSup₂_of_le (f := fun a (_ : a ∈ admissibleSet M.c x) => M.Lop n v x a) a ha le_rfl
  rw [Lop_eq_G M hM n hn hγ hv x a ha.1 ha.2.1, Top_eq_T M hM n hn hγ hv husc x hx] at h
  exact EReal.coe_le_coe_iff.1 h

lemma T_attained (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace) :
    ∃ a ∈ admissibleSet M.c x, G M n v a = T M n v x :=
  ⟨_, th_frontier_adm M hM x hx _ (rule_opt M hM n hn hγ hv husc x hx).1, rfl⟩

lemma T_mono (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x y : ℝ × ℝ) (hx : x ∈ stateSpace)
    (hy : y ∈ stateSpace) (h1 : x.1 ≤ y.1) (h2 : x.2 ≤ y.2) : T M n v x ≤ T M n v y := by
  obtain ⟨a, ha, hGa⟩ := T_attained M hM n hn hγ hv husc x hx
  rw [← hGa]
  exact G_le_T M hM n hn hγ hv husc y hy a (adm_mono hM.2.1 hM.2.2.1 x y h1 h2 a ha)

lemma T_hom (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (l : ℝ) (hl : 0 < l) (x : ℝ × ℝ)
    (hx : x ∈ stateSpace) : T M n v (l * x.1, l * x.2) = l ^ γ * T M n v x := by
  have hlx : ((l * x.1, l * x.2) : ℝ × ℝ) ∈ stateSpace :=
    ⟨mul_nonneg hl.le hx.1, mul_nonneg hl.le hx.2⟩
  apply le_antisymm
  · obtain ⟨b, hb, hGb⟩ := T_attained M hM n hn hγ hv husc _ hlx
    have hb' := adm_scale (c := M.c) _ l⁻¹ (inv_pos.2 hl) b hb
    simp only [inv_mul_cancel_left₀ hl.ne'] at hb'
    have hbb : b = (l * (l⁻¹ * b.1), l * (l⁻¹ * b.2)) := by
      ext <;> simp [hl.ne']
    rw [← hGb, hbb, show G M n v (l * (l⁻¹ * b.1), l * (l⁻¹ * b.2)) =
        l ^ γ * G M n v (l⁻¹ * b.1, l⁻¹ * b.2) from
      G_hom M hM n hn hv l hl (l⁻¹ * b.1, l⁻¹ * b.2) (mul_nonneg (inv_nonneg.2 hl.le) hb.1)
        (mul_nonneg (inv_nonneg.2 hl.le) hb.2.1)]
    exact mul_le_mul_of_nonneg_left (G_le_T M hM n hn hγ hv husc x hx _ hb')
      (Real.rpow_nonneg hl.le _)
  · obtain ⟨a, ha, hGa⟩ := T_attained M hM n hn hγ hv husc x hx
    rw [← hGa, ← G_hom M hM n hn hv l hl a ha.1 ha.2.1]
    exact G_le_T M hM n hn hγ hv husc _ hlx _ (adm_scale _ l hl a ha)

lemma T_concave (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x y : ℝ × ℝ) (hx : x ∈ stateSpace)
    (hy : y ∈ stateSpace) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * T M n v x + (1 - t) * T M n v y ≤
      T M n v (t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2) := by
  obtain ⟨a, ha, hGa⟩ := T_attained M hM n hn hγ hv husc x hx
  obtain ⟨b, hb, hGb⟩ := T_attained M hM n hn hγ hv husc y hy
  have hs : 0 ≤ 1 - t := sub_nonneg.2 ht1
  have hz : ((t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2) : ℝ × ℝ) ∈ stateSpace :=
    ⟨add_nonneg (mul_nonneg ht0 hx.1) (mul_nonneg hs hy.1),
     add_nonneg (mul_nonneg ht0 hx.2) (mul_nonneg hs hy.2)⟩
  rw [← hGa, ← hGb]
  exact (G_concave M hM n hn hγ hv a b ha.1 ha.2.1 hb.1 hb.2.1 t ht0 ht1).trans
    (G_le_T M hM n hn hγ hv husc _ hz _ (adm_convex hM.2.1 x y a b ha hb t ht0 ht1))

lemma T_diag (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N) {γ : ℝ}
    (hγ : γ ≠ 0) {v : ℝ × ℝ → EReal} (hv : IM γ v)
    (husc : UpperSemicontinuousOn v stateSpace) (x : ℝ × ℝ) (hx : x ∈ stateSpace)
    (d : ℕ → ℝ) (hd0 : ∀ k, 0 < d k) (hd1 : ∀ k, d k ≤ 1)
    (hdlim : Filter.Tendsto d Filter.atTop (nhds 0)) (L : ℝ)
    (hL : Filter.Tendsto (fun k => T M n v (x.1 + d k, x.2 + d k)) Filter.atTop (nhds L)) :
    L ≤ T M n v x := by
  have hc0 := hM.2.1
  have hy : ∀ k, ((x.1 + d k, x.2 + d k) : ℝ × ℝ) ∈ stateSpace := fun k =>
    ⟨by linarith [hx.1, hd0 k], by linarith [hx.2, hd0 k]⟩
  choose a ha hGa using fun k => T_attained M hM n hn hγ hv husc _ (hy k)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = x.1 + x.2 + 3 := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hB]; linarith [hx.1, hx.2]
  have hineq : ∀ k, (a k).1 + (a k).2 + M.c * |(a k).2 - x.2| ≤
      x.1 + x.2 + (2 + M.c) * d k := fun k => by
    obtain ⟨-, -, h3⟩ := ha k
    have h3' : (a k).1 + (a k).2 ≤ x.1 + d k + (x.2 + d k) - M.c * |(a k).2 - (x.2 + d k)| := h3
    have e1 := abs_sub_le (a k).2 (x.2 + d k) x.2
    have e2 : |x.2 + d k - x.2| = d k := by rw [add_sub_cancel_left, abs_of_pos (hd0 k)]
    rw [e2] at e1
    nlinarith [mul_le_mul_of_nonneg_left e1 hc0]
  have hsum : ∀ k, (a k).1 + (a k).2 ≤ x.1 + x.2 + 3 := fun k => by
    have := hineq k
    have := mul_nonneg hc0 (abs_nonneg ((a k).2 - x.2))
    have := hd1 k
    have := hd0 k
    nlinarith [hM.2.2.1]
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ × ℝ, ∀ k, b k = (B⁻¹ * (a k).1, B⁻¹ * (a k).2) :=
    ⟨_, fun k => rfl⟩
  have hBb1 : ∀ k, (a k).1 = B * (b k).1 := fun k => by rw [hb k]; simp [hBpos.ne']
  have hBb2 : ∀ k, (a k).2 = B * (b k).2 := fun k => by rw [hb k]; simp [hBpos.ne']
  have hbI : ∀ k, b k ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := fun k => by
    obtain ⟨h1, h2, -⟩ := ha k
    have hs := hsum k
    rw [hb k, Set.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
    refine ⟨⟨mul_nonneg (inv_nonneg.2 hBpos.le) h1, mul_nonneg (inv_nonneg.2 hBpos.le) h2⟩,
      ⟨?_, ?_⟩⟩
    · rw [inv_mul_le_iff₀ hBpos]; rw [hB]; linarith
    · rw [inv_mul_le_iff₀ hBpos]; rw [hB]; linarith
  have hb0 : ∀ k, 0 ≤ (b k).1 ∧ 0 ≤ (b k).2 ∧ (b k).1 ≤ 1 ∧ (b k).2 ≤ 1 := fun k => by
    have h := hbI k
    rw [Set.mem_Icc] at h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  obtain ⟨bl, hbl, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hbI
  have hbl0 : 0 ≤ bl.1 ∧ 0 ≤ bl.2 := by
    rw [Set.mem_Icc] at hbl
    exact ⟨hbl.1.1, hbl.1.2⟩
  have hBg : 0 < B ^ γ := Real.rpow_pos_of_pos hBpos γ
  have hBne : B ^ γ ≠ 0 := hBg.ne'
  have hT : ∀ k, T M n v (x.1 + d k, x.2 + d k) = B ^ γ * G M n v (b k) := fun k => by
    rw [← hGa k, show a k = (B * (b k).1, B * (b k).2) from Prod.ext (hBb1 k) (hBb2 k)]
    exact G_hom M hM n hn hv B hBpos (b k) (hb0 k).1 (hb0 k).2.1
  have hL2 : Filter.Tendsto (fun j => G M n v (b (φ j))) Filter.atTop (nhds (L / B ^ γ)) := by
    have h := (hL.comp hφ.tendsto_atTop).div_const (B ^ γ)
    refine h.congr fun j => ?_
    simp only [Function.comp_apply, hT]
    rw [div_eq_iff hBne]; ring
  have hle := G_usc_seq M hM n hn hγ hv husc (b ∘ φ) bl
    (fun j => ⟨(hb0 (φ j)).1, (hb0 (φ j)).2.2.1⟩)
    (fun j => ⟨(hb0 (φ j)).2.1, (hb0 (φ j)).2.2.2⟩) hbl0.1 hbl0.2 hlim _ hL2
  have hGal : G M n v (B * bl.1, B * bl.2) = B ^ γ * G M n v bl :=
    G_hom M hM n hn hv B hBpos bl hbl0.1 hbl0.2
  have hmem : ((B * bl.1, B * bl.2) : ℝ × ℝ) ∈ admissibleSet M.c x := by
    refine ⟨mul_nonneg hBpos.le hbl0.1, mul_nonneg hBpos.le hbl0.2, ?_⟩
    show B * bl.1 + B * bl.2 ≤ x.1 + x.2 - M.c * |B * bl.2 - x.2|
    have hcont : Continuous (fun p : ℝ × ℝ => B * p.1 + B * p.2 + M.c * |B * p.2 - x.2|) := by
      fun_prop
    have h1 := (hcont.tendsto bl).comp hlim
    have h2 : Filter.Tendsto (fun j => x.1 + x.2 + (2 + M.c) * d (φ j)) Filter.atTop
        (nhds (x.1 + x.2 + (2 + M.c) * 0)) :=
      tendsto_const_nhds.add ((hdlim.comp hφ.tendsto_atTop).const_mul _)
    rw [mul_zero, add_zero] at h2
    have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun j => by
      show B * (b (φ j)).1 + B * (b (φ j)).2 + M.c * |B * (b (φ j)).2 - x.2| ≤ _
      rw [← hBb1, ← hBb2]
      exact hineq (φ j))
    linarith
  have hle' : L ≤ B ^ γ * G M n v bl := by
    have h := mul_le_mul_of_nonneg_left hle hBg.le
    have e : B ^ γ * (L / B ^ γ) = L := by rw [mul_div_assoc', div_eq_iff hBne]; ring
    rwa [e] at h
  calc L ≤ B ^ γ * G M n v bl := hle'
    _ = G M n v (B * bl.1, B * bl.2) := hGal.symm
    _ ≤ T M n v x := G_le_T M hM n hn hγ hv husc x hx _ hmem

theorem p452_step (M : Market Ω) (hM : M.Assumptions) (n : ℕ) (hn : n < M.N)
    (v : ℝ × ℝ → EReal) (hv : IM M.γ v) (husc : UpperSemicontinuousOn v stateSpace) :
    IM M.γ (M.Top n v) ∧ UpperSemicontinuousOn (M.Top n v) stateSpace := by
  have hγ := th_gamma_ne_zero M hM
  have hTE := fun x hx => Top_eq_T M hM n hn hγ hv husc x hx
  have hmono := T_mono M hM n hn hγ hv husc
  have husc' : UpperSemicontinuousOn (M.Top n v) stateSpace := by
    intro x hx y hy
    rw [hTE x hx] at hy
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hy
    have hr1' : T M n v x < r := EReal.coe_lt_coe_iff.1 hr1
    obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, ∀ k, d k = 1 / ((k : ℝ) + 1) := ⟨_, fun k => rfl⟩
    have hd0 : ∀ k, 0 < d k := fun k => by rw [hd]; positivity
    have hd1 : ∀ k, d k ≤ 1 := fun k => by
      rw [hd, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hdanti : Antitone d := fun i j hij => by
      rw [hd, hd]; gcongr <;> exact_mod_cast hij
    have hdlim : Filter.Tendsto d Filter.atTop (nhds 0) := by
      rw [show d = fun k : ℕ => 1 / ((k : ℝ) + 1) from funext hd]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hyk : ∀ k, ((x.1 + d k, x.2 + d k) : ℝ × ℝ) ∈ stateSpace := fun k =>
      ⟨by linarith [hx.1, hd0 k], by linarith [hx.2, hd0 k]⟩
    have hanti : Antitone (fun k => T M n v (x.1 + d k, x.2 + d k)) := fun i j hij =>
      hmono _ _ (hyk j) (hyk i) (by linarith [hdanti hij]) (by linarith [hdanti hij])
    have hbdd : BddBelow (Set.range (fun k => T M n v (x.1 + d k, x.2 + d k))) := by
      refine ⟨T M n v x, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hmono x _ hx (hyk k) (by linarith [hd0 k]) (by linarith [hd0 k])
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hinf := T_diag M hM n hn hγ hv husc x hx d hd0 hd1 hdlim _ hlim
    obtain ⟨k, hk⟩ := exists_lt_of_ciInf_lt (lt_of_le_of_lt hinf hr1')
    have hU : ({p : ℝ × ℝ | p.1 < x.1 + d k} ∩ {p : ℝ × ℝ | p.2 < x.2 + d k}) ∈ nhds x :=
      IsOpen.mem_nhds ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_snd continuous_const))
        ⟨show x.1 < x.1 + d k by linarith [hd0 k], show x.2 < x.2 + d k by linarith [hd0 k]⟩
    filter_upwards [inter_mem_nhdsWithin stateSpace hU] with p hp
    rw [hTE p hp.1]
    calc ((T M n v p : ℝ) : EReal) ≤ ((T M n v (x.1 + d k, x.2 + d k) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.2 (hmono p _ hp.1 (hyk k) (le_of_lt hp.2.1) (le_of_lt hp.2.2))
      _ < (r : EReal) := EReal.coe_lt_coe_iff.2 hk
      _ < y := hr2
  obtain ⟨C, hC0, hC⟩ := lin_bound (T M n v) (fun x hx y hy h1 h2 => hmono x y hx hy h1 h2)
    (fun x hx y hy t ht0 ht1 => T_concave M hM n hn hγ hv husc x y hx hy t ht0 ht1)
  refine ⟨⟨(upperSemicontinuousOn_iff_restrict.2 husc').measurable,
    fun x hx => by rw [hTE x hx]; exact EReal.coe_ne_bot _,
    ⟨C, hC0, fun x hx => by rw [hTE x hx]; exact EReal.coe_le_coe_iff.2 (hC x hx)⟩,
    ?_, ?_, ?_⟩, husc'⟩
  · intro x hx y hy h1 h2
    rw [hTE x hx, hTE y hy]
    exact EReal.coe_le_coe_iff.2 (hmono x y hx hy h1 h2)
  · intro x hx y hy t ht0 ht1
    have hs : 0 ≤ 1 - t := sub_nonneg.2 ht1
    have hz : ((t * x.1 + (1 - t) * y.1, t * x.2 + (1 - t) * y.2) : ℝ × ℝ) ∈ stateSpace :=
      ⟨add_nonneg (mul_nonneg ht0 hx.1) (mul_nonneg hs hy.1),
       add_nonneg (mul_nonneg ht0 hx.2) (mul_nonneg hs hy.2)⟩
    rw [hTE x hx, hTE y hy, hTE _ hz, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (T_concave M hM n hn hγ hv husc x y hx hy t ht0 ht1)
  · intro l hl x hx
    have hlx : ((l * x.1, l * x.2) : ℝ × ℝ) ∈ stateSpace :=
      ⟨mul_nonneg hl.le hx.1, mul_nonneg hl.le hx.2⟩
    rw [hTE x hx, hTE _ hlx, ← EReal.coe_mul, T_hom M hM n hn hγ hv husc l hl x hx]


end P76a

open BauerleRiederMDP.TransactionCosts in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Assumptions) :
    (∀ n ≤ M.N, ConcaveOnE (M.V n) ∧ IncreasingOnE (M.V n) ∧
      HomogeneousOfDegree M.γ (M.V n)) ∧
    (∀ x ∈ stateSpace, M.V M.N x = ((M.U (x.1 + x.2) : ℝ) : EReal)) ∧
    (∀ n < M.N, ∀ x ∈ stateSpace,
      M.V n x = ⨆ a ∈ Set.Icc (0 : ℝ) (x.2 + x.1 / (1 + M.c)),
        M.Lop n (M.V (n + 1)) x (bondAfter M.c x a, a)) ∧
    (∀ n < M.N,
      IsGreatest (M.argmaxPlus n (M.V (n + 1))) (M.aPlus n (M.V (n + 1))) ∧
      IsGreatest (M.argmaxMinus n (M.V (n + 1))) (M.aMinus n (M.V (n + 1))) ∧
      M.qMinus n (M.V (n + 1)) ≤ M.qPlus n (M.V (n + 1))) ∧
    M.IsPolicy 0 M.optimalPolicy ∧
    ∀ n ≤ M.N, ∀ x ∈ stateSpace, M.Vpi M.optimalPolicy n x = M.V n x := by
  exact P76a.glue M hM (P76a.childRI M hM) (P76a.p452_terminal M hM)
    (fun n hn v hv husc => P76a.p452_step M hM n hn v hv husc)
    (fun n hn v hv husc => P76a.childTH_holds M hM n hn v hv husc)
