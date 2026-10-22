-- Prove2me | solution 1 for BNCovPack.SetCover.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:44:22.842331+00:00
-- url     : https://prove2.me/submissions/8e9524df-bfaa-4b7a-ba0e-4d51f3abd583

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_BNCovPack_SetCover_FracScheme



namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

noncomputable def envf (c B : ℝ) (ℓ : ℕ) (L : ℝ) : ℝ :=
  (1 / (ℓ : ℝ)) * (Real.exp (B / (2 * c) * L) - 1)

def FInv {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) : Prop :=
  ∀ s, 0 ≤ st.w s ∧ st.w s ≤ 1 ∧ 0 ≤ st.load s ∧ envf (inst.c s) B ℓ (st.load s) ≤ st.w s

lemma FInv_init {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) : FInv inst B ℓ (FracState.init T) := by
  intro s
  refine ⟨le_rfl, zero_le_one, le_rfl, ?_⟩
  simp [FracState.init, envf]

lemma frac_aug_cont {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) :
    Continuous (fun t => elementWeight inst (augWeight inst B ℓ st e t) e) := by
  have : (fun t => elementWeight inst (augWeight inst B ℓ st e t) e)
      = fun t => ∑ s ∈ inst.elemSets e,
          max (st.w s) (envf (inst.c s) B ℓ (st.load s + t)) := by
    funext t
    unfold elementWeight
    apply Finset.sum_congr rfl
    intro s hs
    simp [augWeight, hs, envf]
  rw [this]
  apply continuous_finset_sum
  intro s _
  unfold envf
  fun_prop

lemma frac_aug_eq {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) (t : ℝ) :
    elementWeight inst (augWeight inst B ℓ st e t) e
      = ∑ s ∈ inst.elemSets e, max (st.w s) (envf (inst.c s) B ℓ (st.load s + t)) := by
  unfold elementWeight
  apply Finset.sum_congr rfl
  intro s hs
  simp [augWeight, hs, envf]

lemma envf_mono {c B : ℝ} (hc : 0 < c) (hB : 0 < B) (ℓ : ℕ) {L L' : ℝ} (h : L ≤ L') :
    envf c B ℓ L ≤ envf c B ℓ L' := by
  unfold envf
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : 0 < B / (2 * c) := by positivity
  have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h this.le)
  linarith

lemma frac_dualStep_spec {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (st : FracState T) (hI : FInv inst B ℓ st) (e : E) (hne : (inst.elemSets e).Nonempty)
    (hlt : elementWeight inst st.w e < 1) :
    0 ≤ dualStep inst B ℓ st e ∧
    1 ≤ elementWeight inst (augWeight inst B ℓ st e (dualStep inst B ℓ st e)) e ∧
    elementWeight inst (augWeight inst B ℓ st e (dualStep inst B ℓ st e)) e ≤ 1 := by
  set F : ℝ → ℝ := fun t => elementWeight inst (augWeight inst B ℓ st e t) e with hF
  have hFc : Continuous F := frac_aug_cont inst B ℓ st e
  set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ 1 ≤ F t} with hA
  have hAc : IsClosed A := isClosed_Ici.inter (isClosed_Ici.preimage hFc)
  have hne' : A.Nonempty := by
    obtain ⟨s0, hs0⟩ := hne
    have hc := inst.hc_pos s0
    have hκ : 0 < B / (2 * inst.c s0) := by positivity
    have hℓpos : (0:ℝ) < ℓ := by exact_mod_cast hℓ
    refine ⟨(ℓ : ℝ) / (B / (2 * inst.c s0)), by positivity, ?_⟩
    show 1 ≤ F _
    rw [hF]
    simp only []
    rw [frac_aug_eq]
    have h1 : max (st.w s0) (envf (inst.c s0) B ℓ (st.load s0 + (ℓ : ℝ) / (B / (2 * inst.c s0))))
        ≤ ∑ s ∈ inst.elemSets e, max (st.w s) (envf (inst.c s) B ℓ (st.load s + (ℓ : ℝ) / (B / (2 * inst.c s0)))) := by
      apply Finset.single_le_sum (f := fun s => max (st.w s) (envf (inst.c s) B ℓ (st.load s + (ℓ : ℝ) / (B / (2 * inst.c s0))))) _ hs0
      intro s _
      exact le_trans (hI s).1 (le_max_left _ _)
    refine le_trans ?_ h1
    refine le_trans ?_ (le_max_right _ _)
    unfold envf
    have hL := (hI s0).2.2.1
    have hexp := Real.add_one_le_exp (B / (2 * inst.c s0) * (st.load s0 + (ℓ : ℝ) / (B / (2 * inst.c s0))))
    have hkey : B / (2 * inst.c s0) * (st.load s0 + (ℓ : ℝ) / (B / (2 * inst.c s0))) ≥ ℓ := by
      rw [mul_add, mul_div_cancel₀ _ hκ.ne']
      have := mul_nonneg hκ.le hL
      linarith
    have : (1:ℝ) ≤ 1 / (ℓ:ℝ) * (Real.exp (B / (2 * inst.c s0) * (st.load s0 + (ℓ : ℝ) / (B / (2 * inst.c s0)))) - 1) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hℓpos]
      linarith
    exact this
  have hbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
  have hy_mem : dualStep inst B ℓ st e ∈ A := by
    have := hAc.csInf_mem hne' hbdd
    exact this
  set y := dualStep inst B ℓ st e with hy
  have hy0 : 0 ≤ y := hy_mem.1
  have hy1 : 1 ≤ F y := hy_mem.2
  have hypos : 0 < y := by
    rcases hy0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hF0 : F 0 = elementWeight inst st.w e := by
        rw [hF]; simp only []
        rw [frac_aug_eq]
        unfold elementWeight
        apply Finset.sum_congr rfl
        intro s _
        rw [add_zero]
        exact max_eq_left (hI s).2.2.2
      rw [← h] at hy1
      rw [hF0] at hy1
      linarith
  have hlt1 : ∀ t ∈ Set.Ico 0 y, F t ≤ 1 := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have : t ∈ A := ⟨ht.1, hcon.le⟩
    have h3 : y ≤ t := csInf_le hbdd this
    linarith [ht.2]
  have hclosed : IsClosed {t : ℝ | F t ≤ 1} := isClosed_Iic.preimage hFc
  have hsub : Set.Icc 0 y ⊆ {t : ℝ | F t ≤ 1} := by
    rw [← closure_Ico hypos.ne]
    exact closure_minimal hlt1 hclosed
  exact ⟨hy0, hy1, hsub ⟨hy0, le_rfl⟩⟩


lemma frac_term {c B : ℝ} (hc : 0 < c) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {w L y : ℝ}
    (hw : envf c B ℓ L ≤ w) (hy : 0 ≤ y) :
    c * (max w (envf c B ℓ (L + y)) - w)
      ≤ (B / 2) * y * (max w (envf c B ℓ (L + y)) + 1 / (ℓ : ℝ)) := by
  have hℓr : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  set κ := B / (2 * c) with hκ
  have hκpos : 0 < κ := by positivity
  have hcκ : c * κ = B / 2 := by rw [hκ]; field_simp
  set p := Real.exp (κ * L) with hp
  set g := Real.exp (κ * y) with hg
  have hp0 : 0 < p := Real.exp_pos _
  have hg1 : 1 ≤ g := Real.one_le_exp (mul_nonneg hκpos.le hy)
  have hpg : Real.exp (κ * (L + y)) = p * g := by
    rw [mul_add, Real.exp_add]
  have hE' : envf c B ℓ (L + y) = (1 / (ℓ : ℝ)) * (p * g - 1) := by
    unfold envf; rw [← hκ, hpg]
  have hE : envf c B ℓ L = (1 / (ℓ : ℝ)) * (p - 1) := by
    unfold envf; rw [← hκ]
  have hdiff : envf c B ℓ (L + y) - envf c B ℓ L = (1 / (ℓ : ℝ)) * p * (g - 1) := by
    rw [hE', hE]; ring
  have hmono : envf c B ℓ L ≤ envf c B ℓ (L + y) := envf_mono hc hB ℓ (by linarith)
  have hA : max w (envf c B ℓ (L + y)) - w ≤ (1 / (ℓ : ℝ)) * p * (g - 1) := by
    rcases le_total w (envf c B ℓ (L + y)) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]
      have : 0 ≤ envf c B ℓ (L + y) - envf c B ℓ L := by linarith
      linarith
  have hgg : g - 1 ≤ κ * y * g := by
    have := Real.add_one_le_exp (-(κ * y))
    have h2 : Real.exp (-(κ * y)) = g⁻¹ := Real.exp_neg _
    rw [h2] at this
    have hgpos : 0 < g := by linarith
    have : (1 - κ * y) * g ≤ 1 := by
      calc (1 - κ * y) * g ≤ g⁻¹ * g := mul_le_mul_of_nonneg_right (by linarith) hgpos.le
        _ = 1 := inv_mul_cancel₀ hgpos.ne'
    nlinarith
  have hmax : envf c B ℓ (L + y) ≤ max w (envf c B ℓ (L + y)) := le_max_right _ _
  calc c * (max w (envf c B ℓ (L + y)) - w)
      ≤ c * ((1 / (ℓ : ℝ)) * p * (g - 1)) := mul_le_mul_of_nonneg_left hA hc.le
    _ ≤ c * ((1 / (ℓ : ℝ)) * p * (κ * y * g)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        apply mul_le_mul_of_nonneg_left hgg (by positivity)
    _ = (B / 2) * y * ((1 / (ℓ : ℝ)) * (p * g)) := by
        rw [← hcκ]; ring
    _ = (B / 2) * y * (envf c B ℓ (L + y) + 1 / (ℓ : ℝ)) := by
        rw [hE']; ring
    _ ≤ (B / 2) * y * (max w (envf c B ℓ (L + y)) + 1 / (ℓ : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith


lemma frac_aug_apply {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (ℓ : ℕ) (st : FracState T) (e : E) (t : ℝ) (s : T) :
    augWeight inst B ℓ st e t s
      = if s ∈ inst.elemSets e then max (st.w s) (envf (inst.c s) B ℓ (st.load s + t)) else st.w s := by
  unfold augWeight envf
  rfl

lemma frac_step_spec {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (st : FracState T) (hI : FInv inst B ℓ st) (e : E) (hne : (inst.elemSets e).Nonempty)
    (hcard : (inst.elemSets e).card ≤ ℓ) :
    FInv inst B ℓ (fracStep inst B ℓ st e) ∧
    (∀ s, st.w s ≤ (fracStep inst B ℓ st e).w s) ∧
    1 ≤ elementWeight inst (fracStep inst B ℓ st e).w e ∧
    (∑ s, inst.c s * (fracStep inst B ℓ st e).w s - B * (fracStep inst B ℓ st e).dual
      ≤ ∑ s, inst.c s * st.w s - B * st.dual) ∧
    (∀ w'' : T → ℝ, (∀ s, 0 ≤ w'' s) → 1 ≤ elementWeight inst w'' e →
      ∑ s, w'' s * st.load s - st.dual
        ≤ ∑ s, w'' s * (fracStep inst B ℓ st e).load s - (fracStep inst B ℓ st e).dual) := by
  by_cases h : 1 ≤ elementWeight inst st.w e
  · have : fracStep inst B ℓ st e = st := by
      unfold fracStep; rw [if_pos h]
    rw [this]
    exact ⟨hI, fun _ => le_rfl, h, le_rfl, fun _ _ _ => le_rfl⟩
  · push_neg at h
    obtain ⟨hy0, hy1, hy2⟩ := frac_dualStep_spec inst B hB ℓ hℓ st hI e hne h
    set y := dualStep inst B ℓ st e with hy
    have hstep : fracStep inst B ℓ st e = FracState.mk (augWeight inst B ℓ st e y)
        (fun s => if s ∈ inst.elemSets e then st.load s + y else st.load s)
        (st.dual + y) := by
      unfold fracStep; rw [if_neg (not_le.mpr h)]
    rw [hstep]
    simp only []
    have hge : ∀ s, st.w s ≤ augWeight inst B ℓ st e y s := by
      intro s
      rw [frac_aug_apply]
      split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    have hnn : ∀ s, 0 ≤ augWeight inst B ℓ st e y s := fun s => le_trans (hI s).1 (hge s)
    have hle1 : ∀ s ∈ inst.elemSets e, augWeight inst B ℓ st e y s ≤ 1 := by
      intro s hs
      refine le_trans ?_ hy2
      unfold elementWeight
      exact Finset.single_le_sum (f := fun t => augWeight inst B ℓ st e y t) (fun t _ => hnn t) hs
    refine ⟨?_, hge, hy1, ?_, ?_⟩
    · intro s
      by_cases hs : s ∈ inst.elemSets e
      · simp only [hs, if_true]
        refine ⟨hnn s, hle1 s hs, by linarith [(hI s).2.2.1], ?_⟩
        rw [frac_aug_apply, if_pos hs]
        exact le_max_right _ _
      · simp only [hs, if_false]
        rw [frac_aug_apply, if_neg hs]
        exact hI s
    · -- primal
      have hterm : ∀ s, inst.c s * (augWeight inst B ℓ st e y s - st.w s)
          ≤ if s ∈ inst.elemSets e then (B / 2) * y * (augWeight inst B ℓ st e y s + 1 / (ℓ : ℝ)) else 0 := by
        intro s
        by_cases hs : s ∈ inst.elemSets e
        · rw [if_pos hs]
          have := frac_term (inst.hc_pos s) hB ℓ hℓ (hI s).2.2.2 hy0
          rw [frac_aug_apply, if_pos hs]
          exact this
        · rw [if_neg hs, frac_aug_apply, if_neg hs]; simp
      have hsum : ∑ s, inst.c s * (augWeight inst B ℓ st e y s - st.w s) ≤ B * y := by
        calc ∑ s, inst.c s * (augWeight inst B ℓ st e y s - st.w s)
            ≤ ∑ s, (if s ∈ inst.elemSets e then (B / 2) * y * (augWeight inst B ℓ st e y s + 1 / (ℓ : ℝ)) else 0) :=
              Finset.sum_le_sum (fun s _ => hterm s)
          _ = ∑ s ∈ inst.elemSets e, (B / 2) * y * (augWeight inst B ℓ st e y s + 1 / (ℓ : ℝ)) := by
              rw [Finset.sum_ite_mem]; simp
          _ = (B / 2) * y * (elementWeight inst (augWeight inst B ℓ st e y) e
                + (inst.elemSets e).card * (1 / (ℓ : ℝ))) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp [elementWeight]
          _ ≤ (B / 2) * y * (1 + 1) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hℓr : (0:ℝ) < ℓ := by exact_mod_cast hℓ
              have : ((inst.elemSets e).card : ℝ) * (1 / (ℓ : ℝ)) ≤ 1 := by
                rw [← div_eq_mul_one_div, div_le_one hℓr]
                exact_mod_cast hcard
              linarith
          _ = B * y := by ring
      have : ∑ s, inst.c s * augWeight inst B ℓ st e y s
          = ∑ s, inst.c s * st.w s + ∑ s, inst.c s * (augWeight inst B ℓ st e y s - st.w s) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro s _; ring
      rw [this]
      linarith
    · intro w'' hw''0 hw''1
      have hload : ∑ s, w'' s * (if s ∈ inst.elemSets e then st.load s + y else st.load s)
          = ∑ s, w'' s * st.load s + y * ∑ s ∈ inst.elemSets e, w'' s := by
        have : ∀ s, w'' s * (if s ∈ inst.elemSets e then st.load s + y else st.load s)
            = w'' s * st.load s + y * (if s ∈ inst.elemSets e then w'' s else 0) := by
          intro s; split_ifs <;> ring
        simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_ite_mem]; simp
      have : 1 ≤ ∑ s ∈ inst.elemSets e, w'' s := hw''1
      have := mul_le_mul_of_nonneg_left this hy0
      show _ ≤ ∑ s, w'' s * (if s ∈ inst.elemSets e then st.load s + y else st.load s) - (st.dual + y)
      rw [hload]
      linarith


lemma frac_run_spec {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (σ : List E) (hσ : ∀ e ∈ σ, (inst.elemSets e).Nonempty ∧ (inst.elemSets e).card ≤ ℓ)
    (st : FracState T) (hI : FInv inst B ℓ st) :
    FInv inst B ℓ (σ.foldl (fracStep inst B ℓ) st) ∧
    (∀ s, st.w s ≤ (σ.foldl (fracStep inst B ℓ) st).w s) ∧
    (∀ e ∈ σ, 1 ≤ elementWeight inst (σ.foldl (fracStep inst B ℓ) st).w e) ∧
    (∑ s, inst.c s * (σ.foldl (fracStep inst B ℓ) st).w s
        - B * (σ.foldl (fracStep inst B ℓ) st).dual
      ≤ ∑ s, inst.c s * st.w s - B * st.dual) ∧
    (∀ w'' : T → ℝ, (∀ s, 0 ≤ w'' s) → (∀ e ∈ σ, 1 ≤ elementWeight inst w'' e) →
      ∑ s, w'' s * st.load s - st.dual
        ≤ ∑ s, w'' s * (σ.foldl (fracStep inst B ℓ) st).load s
          - (σ.foldl (fracStep inst B ℓ) st).dual) := by
  induction σ generalizing st with
  | nil =>
    exact ⟨hI, fun _ => le_rfl, fun e he => by simp at he, le_rfl, fun _ _ _ => le_rfl⟩
  | cons x τ ih =>
    have hx := hσ x (List.mem_cons_self)
    obtain ⟨a1, a2, a3, a4, a5⟩ := frac_step_spec inst B hB ℓ hℓ st hI x hx.1 hx.2
    obtain ⟨b1, b2, b3, b4, b5⟩ := ih (fun e he => hσ e (List.mem_cons_of_mem _ he))
      (fracStep inst B ℓ st x) a1
    simp only [List.foldl_cons]
    refine ⟨b1, fun s => le_trans (a2 s) (b2 s), ?_, by linarith, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · refine le_trans a3 ?_
        unfold elementWeight
        exact Finset.sum_le_sum (fun s _ => b2 s)
      · exact b3 e he
    · intro w'' hw''0 hw''1
      have := a5 w'' hw''0 (hw''1 x (List.mem_cons_self))
      have := b5 w'' hw''0 (fun e he => hw''1 e (List.mem_cons_of_mem _ he))
      linarith

lemma frac_load_bound {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (st : FracState T) (hI : FInv inst B ℓ st) (s : T) :
    st.load s ≤ 2 * inst.c s * Real.log (1 + (ℓ : ℝ)) / B := by
  obtain ⟨_, h1, hL, henv⟩ := hI s
  have hℓr : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  have hc := inst.hc_pos s
  unfold envf at henv
  have h2 : Real.exp (B / (2 * inst.c s) * st.load s) ≤ 1 + ℓ := by
    have : (1 / (ℓ : ℝ)) * (Real.exp (B / (2 * inst.c s) * st.load s) - 1) ≤ 1 := le_trans henv h1
    rw [one_div, ← div_eq_inv_mul, div_le_one hℓr] at this
    linarith
  have h3 : B / (2 * inst.c s) * st.load s ≤ Real.log (1 + (ℓ : ℝ)) := by
    rw [← Real.exp_le_exp, Real.exp_log (by linarith)]
    exact h2
  have hκ : 0 < B / (2 * inst.c s) := by positivity
  rw [le_div_iff₀ hB]
  have : st.load s * B ≤ 2 * inst.c s * Real.log (1 + (ℓ : ℝ)) := by
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * inst.c s)
    have h5 : 2 * inst.c s * (B / (2 * inst.c s) * st.load s) = B * st.load s := by
      field_simp
    linarith
  linarith

lemma frac_core {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (σ : List E) (hfreq : ∀ e ∈ σ, (inst.elemSets e).card ≤ ℓ)
    (hσ : ∀ e ∈ σ, (inst.elemSets e).Nonempty) :
    (∀ e ∈ σ, 1 ≤ elementWeight inst (fracRun inst B ℓ σ).w e) ∧
    ∀ w'' : T → ℝ, (∀ s, 0 ≤ w'' s) → (∀ e ∈ σ, 1 ≤ elementWeight inst w'' e) →
      ∑ s, inst.c s * (fracRun inst B ℓ σ).w s
        ≤ 2 * Real.log (1 + (ℓ : ℝ)) * ∑ s, inst.c s * w'' s := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := frac_run_spec inst B hB ℓ hℓ σ
    (fun e he => ⟨hσ e he, hfreq e he⟩) (FracState.init T) (FInv_init inst B ℓ)
  refine ⟨b3, ?_⟩
  intro w'' hw''0 hw''1
  have hb5 := b5 w'' hw''0 hw''1
  have hinit : ∑ s, inst.c s * (FracState.init T).w s = 0 := by simp [FracState.init]
  have hinit2 : ∑ s, w'' s * (FracState.init T).load s = 0 := by simp [FracState.init]
  have hinit3 : (FracState.init T).dual = 0 := rfl
  rw [hinit, hinit3] at b4
  rw [hinit2, hinit3] at hb5
  have hlb := frac_load_bound inst B hB ℓ hℓ (σ.foldl (fracStep inst B ℓ) (FracState.init T)) b1
  have hsum : ∑ s, w'' s * (σ.foldl (fracStep inst B ℓ) (FracState.init T)).load s
      ≤ ∑ s, w'' s * (2 * inst.c s * Real.log (1 + (ℓ : ℝ)) / B) :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hlb s) (hw''0 s))
  have hsum2 : ∑ s, w'' s * (2 * inst.c s * Real.log (1 + (ℓ : ℝ)) / B)
      = (2 * Real.log (1 + (ℓ : ℝ)) / B) * ∑ s, inst.c s * w'' s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; ring
  unfold fracRun
  have hd : (σ.foldl (fracStep inst B ℓ) (FracState.init T)).dual
      ≤ (2 * Real.log (1 + (ℓ : ℝ)) / B) * ∑ s, inst.c s * w'' s := by linarith
  have := mul_le_mul_of_nonneg_left hd hB.le
  have e2 : B * ((2 * Real.log (1 + (ℓ : ℝ)) / B) * ∑ s, inst.c s * w'' s)
      = 2 * Real.log (1 + (ℓ : ℝ)) * ∑ s, inst.c s * w'' s := by
    field_simp
  linarith

end BNCovPack.SetCover

open BNCovPack.SetCover
open OnlinePrimalDual.OnlineSetCover

theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (σ : List E) (hfreq : ∀ e ∈ σ, (inst.elemSets e).card ≤ ℓ)
    (hσ : ∀ e ∈ σ, (inst.elemSets e).Nonempty) :
    (∀ e ∈ σ, 1 ≤ elementWeight inst (fracRun inst B ℓ σ).w e) ∧
    ∀ w'' : T → ℝ, (∀ s, 0 ≤ w'' s) → (∀ e ∈ σ, 1 ≤ elementWeight inst w'' e) →
      ∑ s, inst.c s * (fracRun inst B ℓ σ).w s
        ≤ 2 * Real.log (1 + (ℓ : ℝ)) * ∑ s, inst.c s * w'' s := by
  exact frac_core inst B hB ℓ hℓ σ hfreq hσ
