-- Prove2me | solution 1 for BNCovPack.SetCover.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:47:33.441151+00:00
-- url     : https://prove2.me/submissions/3468be80-8099-4fa6-b0f4-1b4ee692a757

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_BNCovPack_SetCover_Potential
import Definitions.Def_BNCovPack_SetCover_Algorithm



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




lemma pot_prod_clamp {ι : Type*} [DecidableEq ι] (S : Finset ι) (f f' : ι → ℝ) (v : ℝ)
    (h0 : ∀ i ∈ S, 0 ≤ f i) (hff : ∀ i ∈ S, f i ≤ f' i) (hf1 : ∀ i ∈ S, f' i ≤ 1)
    (hv' : ∀ i ∈ S, f' i ≤ v * f i) :
    1 - ∏ i ∈ S, (1 - f' i) ≤ v * (1 - ∏ i ∈ S, (1 - f i)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hff i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hv' i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hA : 0 ≤ ∏ i ∈ S, (1 - f i) :=
      Finset.prod_nonneg (fun i hi => by
        have := hff i (Finset.mem_insert_of_mem hi)
        have := hf1 i (Finset.mem_insert_of_mem hi)
        linarith)
    have hA' : 0 ≤ ∏ i ∈ S, (1 - f' i) :=
      Finset.prod_nonneg (fun i hi => by
        have := hf1 i (Finset.mem_insert_of_mem hi)
        linarith)
    have hle : ∏ i ∈ S, (1 - f' i) ≤ ∏ i ∈ S, (1 - f i) :=
      Finset.prod_le_prod (fun i hi => by
        have := hf1 i (Finset.mem_insert_of_mem hi)
        linarith) (fun i hi => by
        have := hff i (Finset.mem_insert_of_mem hi)
        linarith)
    have ha0 := h0 a (Finset.mem_insert_self a S)
    have haff := hff a (Finset.mem_insert_self a S)
    have hav := hv' a (Finset.mem_insert_self a S)
    have h1 : f' a * ∏ i ∈ S, (1 - f' i) ≤ v * f a * ∏ i ∈ S, (1 - f i) := by
      calc f' a * ∏ i ∈ S, (1 - f' i) ≤ f' a * ∏ i ∈ S, (1 - f i) :=
            mul_le_mul_of_nonneg_left hle (by linarith)
        _ ≤ v * f a * ∏ i ∈ S, (1 - f i) := mul_le_mul_of_nonneg_right hav hA
    nlinarith

lemma pot_elementWeight_update {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (s : T) (δ : ℝ) (e : E) :
    elementWeight inst (Function.update w s (w s + δ)) e
      = elementWeight inst w e + (if s ∈ inst.elemSets e then δ else 0) := by
  unfold elementWeight
  have : ∀ t, Function.update w s (w s + δ) t = w t + (if t = s then δ else 0) := by
    intro t
    by_cases h : t = s
    · subst h; simp
    · simp [Function.update_of_ne h, h]
  simp only [this, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

lemma pot_fval_update {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (w : T → ℝ) (s : T) (δ : ℝ) (hδ : 0 ≤ δ)
    (e : E) :
    fval inst α w e ≤ fval inst α (Function.update w s (w s + δ)) e ∧
    fval inst α (Function.update w s (w s + δ)) e ≤ Real.exp (α * δ) * fval inst α w e ∧
    (s ∉ inst.elemSets e → fval inst α (Function.update w s (w s + δ)) e = fval inst α w e) ∧
    fval inst α (Function.update w s (w s + δ)) e ≤ 1 ∧ 0 ≤ fval inst α w e := by
  unfold fval
  rw [pot_elementWeight_update]
  have hg : 0 < Real.exp (-α + α * elementWeight inst w e) := Real.exp_pos _
  have hv : 1 ≤ Real.exp (α * δ) := Real.one_le_exp (mul_nonneg hα hδ)
  refine ⟨?_, ?_, ?_, min_le_left _ _, le_min zero_le_one hg.le⟩
  · by_cases hs : s ∈ inst.elemSets e
    · simp only [hs, if_true]
      apply min_le_min le_rfl
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα hδ]
    · simp [hs]
  · by_cases hs : s ∈ inst.elemSets e
    · simp only [hs, if_true]
      have : Real.exp (-α + α * (elementWeight inst w e + δ))
          = Real.exp (α * δ) * Real.exp (-α + α * elementWeight inst w e) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      set g := Real.exp (-α + α * elementWeight inst w e)
      set v := Real.exp (α * δ)
      rcases le_total g 1 with h | h
      · rw [min_eq_right h]; exact min_le_right _ _
      · rw [min_eq_left h]
        calc min 1 (v * g) ≤ 1 := min_le_left _ _
          _ ≤ v * 1 := by linarith
    · simp only [hs, if_false, add_zero]
      have : (1:ℝ) ≤ Real.exp (α * δ) := hv
      have h0 : 0 ≤ min 1 (Real.exp (-α + α * elementWeight inst w e)) := le_min zero_le_one hg.le
      nlinarith
  · intro hs
    simp [hs]

lemma pot_potential2_update_not_mem {T : Type*} [Fintype T] [DecidableEq T]
    (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) (hs : s ∉ C) :
    potential2 α OPT (Function.update w s (w s + δ)) (insert s C)
      = 2 * Real.exp (-(α * δ)) * potential2 α OPT w C := by
  unfold potential2
  have key : ∑ t, (Real.log 2 * (if t ∈ insert s C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t) - (OPT : ℝ)
      = (∑ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t) - (OPT : ℝ))
        + (Real.log 2 - α * δ) := by
    have : ∀ t, (Real.log 2 * (if t ∈ insert s C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t)
        = (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t)
          + (if t = s then Real.log 2 - α * δ else 0) := by
      intro t
      by_cases h : t = s
      · subst h; simp [hs]; ring
      · simp [Function.update_of_ne h, h]
    simp only [this, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
    ring
  have h2 : Real.exp (Real.log 2 - α * δ) = 2 * Real.exp (-(α * δ)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
  rw [key, Real.exp_add _ (Real.log 2 - α * δ), h2]
  ring

lemma pot_potential2_update {T : Type*} [Fintype T] [DecidableEq T]
    (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) :
    potential2 α OPT (Function.update w s (w s + δ)) C
      = Real.exp (-(α * δ)) * potential2 α OPT w C := by
  unfold potential2
  have key : ∑ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t) - (OPT : ℝ)
      = (∑ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t) - (OPT : ℝ))
        + (-(α * δ)) := by
    have : ∀ t, (Real.log 2 * (if t ∈ C then (1:ℝ) else 0)
        - α * Function.update w s (w s + δ) t)
        = (Real.log 2 * (if t ∈ C then (1:ℝ) else 0) - α * w t)
          + (if t = s then -(α * δ) else 0) := by
      intro t
      by_cases h : t = s
      · subst h; simp; ring
      · simp [Function.update_of_ne h, h]
    simp only [this, Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq']
    ring
  rw [key, Real.exp_add]
  ring


open Classical in
lemma pot_p1_split {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (C : Finset T) (s : T) :
    potential1 inst α w C
      = 1 - (∏ e ∈ (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∉ inst.elemSets e), (1 - fval inst α w e))
          * ∏ e ∈ (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∈ inst.elemSets e), (1 - fval inst α w e) := by
  unfold potential1
  rw [← Finset.prod_filter_not_mul_prod_filter (s := Finset.univ.filter (fun e => ¬ coveredBy inst C e))
    (p := fun e => s ∈ inst.elemSets e)]

open Classical in
lemma pot_p1_insert {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (C : Finset T) (s : T) :
    potential1 inst α w (insert s C)
      = 1 - ∏ e ∈ (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∉ inst.elemSets e), (1 - fval inst α w e) := by
  unfold potential1
  have hset : Finset.univ.filter (fun e => ¬ coveredBy inst (insert s C) e)
      = (Finset.univ.filter (fun e => ¬ coveredBy inst C e)).filter
              (fun e => s ∉ inst.elemSets e) := by
    ext e
    have key : coveredBy inst (insert s C) e ↔ coveredBy inst C e ∨ s ∈ inst.elemSets e := by
      constructor
      · rintro ⟨t, ht, htC⟩
        rcases Finset.mem_insert.mp htC with rfl | htC
        · exact Or.inr ht
        · exact Or.inl ⟨t, ht, htC⟩
      · rintro (⟨t, ht, htC⟩ | h)
        · exact ⟨t, ht, Finset.mem_insert_of_mem htC⟩
        · exact ⟨s, h, Finset.mem_insert_self _ _⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, key]
    tauto
  rw [hset]

lemma pot_pos {T : Type*} [Fintype T] [DecidableEq T] (α : ℝ) (OPT : ℕ) (w : T → ℝ) (C : Finset T) :
    0 < potential2 α OPT w C := Real.exp_pos _

open Classical in
lemma pot_core_ii {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ)
    (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) (hδ : 0 ≤ δ) :
    potential inst α OPT (Function.update w s (w s + δ)) (insert s C) ≤ potential inst α OPT w C ∨
    potential inst α OPT (Function.update w s (w s + δ)) C ≤ potential inst α OPT w C := by
  set w' := Function.update w s (w s + δ) with hw'
  set S₀ := Finset.univ.filter (fun e => ¬ coveredBy inst C e) with hS₀
  set Bs := S₀.filter (fun e => s ∉ inst.elemSets e) with hBs
  set As := S₀.filter (fun e => s ∈ inst.elemSets e) with hAs
  have hf := fun e => pot_fval_update inst α hα w s δ hδ e
  have hX := pot_pos α OPT w C
  have hu0 : 0 < Real.exp (-(α * δ)) := Real.exp_pos _
  have hu1 : Real.exp (-(α * δ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hα hδ])
  have hBeq : ∏ e ∈ Bs, (1 - fval inst α w' e) = ∏ e ∈ Bs, (1 - fval inst α w e) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [(hf e).2.2.1 (Finset.mem_filter.mp he).2]
  have hsplit := pot_p1_split inst α w C s
  have hsplit' := pot_p1_split inst α w' C s
  rw [← hS₀, ← hBs, ← hAs] at hsplit hsplit'
  rw [hBeq] at hsplit'
  set P := ∏ e ∈ Bs, (1 - fval inst α w e) with hP
  have hf1 : ∀ e, fval inst α w e ≤ 1 := fun e => min_le_left _ _
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun e he => by
    have := hf1 e; linarith)
  have hv1 : 1 ≤ Real.exp (α * δ) := Real.one_le_exp (mul_nonneg hα hδ)
  have huv : Real.exp (-(α * δ)) * Real.exp (α * δ) = 1 := by
    rw [← Real.exp_add]; simp
  set u := Real.exp (-(α * δ)) with hu
  set v := Real.exp (α * δ) with hv
  set X := potential2 α OPT w C with hXdef
  have hp2 : potential2 α OPT w' C = u * X := pot_potential2_update α OPT w C s δ
  by_cases hsC : s ∈ C
  · right
    have hAs_empty : As = ∅ := by
      rw [hAs, Finset.filter_eq_empty_iff]
      intro e he hse
      have := (Finset.mem_filter.mp he).2
      exact this ⟨s, hse, hsC⟩
    rw [hAs_empty, Finset.prod_empty, mul_one] at hsplit hsplit'
    unfold potential
    rw [hsplit, hsplit', hp2]
    nlinarith [mul_le_mul_of_nonneg_right hu1 hX.le]
  · have hp2' : potential2 α OPT w' (insert s C) = 2 * u * X :=
      pot_potential2_update_not_mem α OPT w C s δ hsC
    have hins := pot_p1_insert inst α w' C s
    rw [← hS₀, ← hBs, hBeq] at hins
    set Q := ∏ e ∈ As, (1 - fval inst α w e) with hQ
    set Q' := ∏ e ∈ As, (1 - fval inst α w' e) with hQ'
    have hclamp : 1 - Q' ≤ v * (1 - Q) := by
      apply pot_prod_clamp As (fun e => fval inst α w e) (fun e => fval inst α w' e) v
      · intro e _; exact (hf e).2.2.2.2
      · intro e _; exact (hf e).1
      · intro e _; exact (hf e).2.2.2.1
      · intro e _; exact (hf e).2.1
    have hclamp2 : u - u * Q' ≤ 1 - Q := by
      have h1 := mul_le_mul_of_nonneg_left hclamp hu0.le
      have h2 : u * (v * (1 - Q)) = 1 - Q := by rw [← mul_assoc, huv, one_mul]
      nlinarith
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    unfold potential at h1 h2
    rw [hins, hp2'] at h1
    rw [hsplit', hp2] at h2
    rw [hsplit] at h1 h2
    have e1 : 0 ≤ P * (1 - u + u * Q' - Q) := mul_nonneg hP0 (by linarith)
    have e2 : 0 ≤ X * (1 - u) ^ 2 := mul_nonneg hX.le (sq_nonneg _)
    nlinarith [mul_pos hu0 hu0, mul_nonneg hu0.le (sub_nonneg.mpr hu1)]




lemma poti_e_gt_two : 2 < Real.exp 1 := by
  have := Real.add_one_lt_exp (x := 1) (by norm_num)
  linarith

lemma poti_L_pos : 0 < Real.log (Real.exp 1 / (Real.exp 1 - 1)) := by
  have h := poti_e_gt_two
  apply Real.log_pos
  rw [lt_div_iff₀ (by linarith)]
  linarith

lemma poti_r_pos : 0 < rConst := by
  unfold rConst
  exact mul_pos (Real.exp_pos 1) poti_L_pos

lemma poti_chord (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ Real.exp (-1)) :
    -(rConst * q) ≤ Real.log (1 - q) := by
  have he := poti_e_gt_two
  set e := Real.exp 1 with hedef
  have hinv : Real.exp (-1) = e⁻¹ := Real.exp_neg 1
  rw [hinv] at hq1
  have hepos : 0 < e := by linarith
  set t := q * e with ht
  have ht0 : 0 ≤ t := mul_nonneg hq0 hepos.le
  have ht1 : t ≤ 1 := by
    have : q * e ≤ e⁻¹ * e := mul_le_mul_of_nonneg_right hq1 hepos.le
    rwa [inv_mul_cancel₀ hepos.ne'] at this
  have hconc := strictConcaveOn_log_Ioi.concaveOn
  have hy : 0 < 1 - e⁻¹ := by
    have : e⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  have := hconc.2 (Set.mem_Ioi.mpr (one_pos : (0:ℝ) < 1)) (Set.mem_Ioi.mpr hy)
    (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at this
  have h1 : 1 - t + t * (1 - e⁻¹) = 1 - q := by
    rw [ht]; field_simp; ring
  rw [h1] at this
  have h2 : Real.log (1 - e⁻¹) = -Real.log (e / (e - 1)) := by
    have : 1 - e⁻¹ = (e / (e - 1))⁻¹ := by
      field_simp [show e - 1 ≠ 0 by linarith]
    rw [this, Real.log_inv]
  rw [h2] at this
  have h3 : rConst * q = t * Real.log (e / (e - 1)) := by
    unfold rConst
    rw [← hedef, ht]; ring
  rw [h3]
  linarith

lemma poti_key (n OPT : ℕ) (hOPT : 1 ≤ OPT) :
    Real.exp (-(OPT : ℝ)) ≤ (1 - Real.exp (-(alphaParam n OPT))) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]
    exact Real.exp_le_one_iff.mpr (by simp)
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hOPTpos : (0:ℝ) < OPT := by exact_mod_cast hOPT
  have hr := poti_r_pos
  set x := rConst * (n : ℝ) / (OPT : ℝ) with hx
  have hxpos : 0 < x := by positivity
  set q := Real.exp (-(alphaParam n OPT)) with hq
  have hα1 : 1 ≤ alphaParam n OPT := le_max_left _ _
  have hαx : Real.log x ≤ alphaParam n OPT := le_max_right _ _
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hqx : q ≤ x⁻¹ := by
    rw [hq, ← Real.exp_log (inv_pos.mpr hxpos), Real.log_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnrq : (n : ℝ) * (rConst * q) ≤ OPT := by
    have : rConst * q ≤ rConst * x⁻¹ := mul_le_mul_of_nonneg_left hqx hr.le
    have h2 : (n : ℝ) * (rConst * x⁻¹) = OPT := by
      rw [hx]; field_simp
    nlinarith
  have hchord := poti_chord q hq0.le hq1
  have hq_lt : q < 1 := by
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have h1q : 0 < 1 - q := by linarith
  calc Real.exp (-(OPT : ℝ)) ≤ Real.exp ((n : ℝ) * Real.log (1 - q)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = (1 - q) ^ n := by
        rw [Real.exp_nat_mul, Real.exp_log h1q]

lemma poti_fval_nonneg_le {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (w : T → ℝ) (e : E) :
    0 ≤ fval inst α w e ∧ fval inst α w e ≤ 1 :=
  ⟨le_min zero_le_one (Real.exp_pos _).le, min_le_left _ _⟩

lemma pot_core_i {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (OPT : ℕ) (hOPT : 1 ≤ OPT) :
    potential inst (alphaParam (Fintype.card E) OPT) OPT (fun _ => 0) ∅ ≤ 1 ∧
    ∀ (α : ℝ) (w : T → ℝ) (C : Finset T), 0 < potential inst α OPT w C := by
  classical
  constructor
  · unfold potential potential1 potential2
    have hα1 : 1 ≤ alphaParam (Fintype.card E) OPT := le_max_left _ _
    have hfv : ∀ e, fval inst (alphaParam (Fintype.card E) OPT) (fun _ => (0:ℝ)) e
        = Real.exp (-(alphaParam (Fintype.card E) OPT)) := by
      intro e
      unfold fval elementWeight
      simp only [Finset.sum_const_zero, mul_zero, add_zero]
      apply min_eq_right
      apply Real.exp_le_one_iff.mpr
      linarith
    have hcov : ∀ e, ¬ coveredBy inst (∅ : Finset T) e := by
      rintro e ⟨t, _, ht⟩
      simp at ht
    have hfilter : Finset.univ.filter (fun e => ¬ coveredBy inst (∅ : Finset T) e) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro e _; exact hcov e
    rw [hfilter]
    simp only [hfv, Finset.prod_const, Finset.card_univ]
    have := poti_key (Fintype.card E) OPT hOPT
    have h2 : (∑ s : T, (Real.log 2 * (if s ∈ (∅ : Finset T) then (1:ℝ) else 0)
        - alphaParam (Fintype.card E) OPT * (fun _ : T => (0:ℝ)) s) - (OPT : ℝ)) = -(OPT : ℝ) := by
      simp
    rw [h2]
    linarith
  · intro α w C
    have h2 : 0 < potential2 α OPT w C := Real.exp_pos _
    have h1 : 0 ≤ potential1 inst α w C := by
      classical
      unfold potential1
      have : ∏ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e), (1 - fval inst α w e) ≤ 1 :=
        Finset.prod_le_one (fun e _ => by
          have := (poti_fval_nonneg_le inst α w e).2; linarith)
          (fun e _ => by
          have := (poti_fval_nonneg_le inst α w e).1; linarith)
      linarith
    unfold potential
    linarith



lemma alpha_ge_one (n OPT : ℕ) : 1 ≤ alphaParam n OPT := le_max_left _ _

lemma augmentSet_spec {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ) (w' : T → ℝ)
    (p : (T → ℝ) × Finset T) (hle : ∀ s, p.1 s ≤ w' s) (x : T) :
    (∀ s, (augmentSet inst α OPT w' p x).1 s ≤ w' s) ∧
    (augmentSet inst α OPT w' p x).1 x = w' x ∧
    (∀ s, s ≠ x → (augmentSet inst α OPT w' p x).1 s = p.1 s) ∧
    potential inst α OPT (augmentSet inst α OPT w' p x).1 (augmentSet inst α OPT w' p x).2
      ≤ potential inst α OPT p.1 p.2 ∧
    p.2 ⊆ (augmentSet inst α OPT w' p x).2 := by
  unfold augmentSet
  by_cases hlt : p.1 x < w' x
  · rw [if_pos hlt]
    have hw₁ : Function.update p.1 x (w' x) = Function.update p.1 x (p.1 x + (w' x - p.1 x)) := by
      congr 1; ring
    have hcore := pot_core_ii inst α hα OPT p.1 p.2 x (w' x - p.1 x) (by linarith)
    rw [← hw₁] at hcore
    have hupd1 : ∀ s, Function.update p.1 x (w' x) s ≤ w' s := by
      intro s
      by_cases hs : s = x
      · subst hs; simp
      · rw [Function.update_of_ne hs]; exact hle s
    have hupd2 : ∀ s, s ≠ x → Function.update p.1 x (w' x) s = p.1 s := fun s hs =>
      Function.update_of_ne hs _ _
    by_cases hcond : x ∉ p.2 ∧
        potential inst α OPT (Function.update p.1 x (w' x)) (insert x p.2) ≤ potential inst α OPT p.1 p.2
    · rw [if_pos hcond]
      exact ⟨hupd1, by simp, hupd2, hcond.2, Finset.subset_insert _ _⟩
    · rw [if_neg hcond]
      refine ⟨hupd1, by simp, hupd2, ?_, subset_rfl⟩
      by_cases hx : x ∈ p.2
      · rw [Finset.insert_eq_of_mem hx] at hcore
        rcases hcore with h | h <;> exact h
      · rcases hcore with h | h
        · exact absurd ⟨hx, h⟩ hcond
        · exact h
  · rw [if_neg hlt]
    have heq : p.1 x = w' x := le_antisymm (hle x) (not_lt.mp hlt)
    exact ⟨hle, heq, fun _ _ => rfl, le_rfl, subset_rfl⟩

lemma aug_fold {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ) (w' : T → ℝ)
    (ord : List T) :
    ∀ (p : (T → ℝ) × Finset T), (∀ s, p.1 s ≤ w' s) →
    (∀ s, (ord.foldl (augmentSet inst α OPT w') p).1 s ≤ w' s) ∧
    (∀ s ∈ ord, (ord.foldl (augmentSet inst α OPT w') p).1 s = w' s) ∧
    (∀ s, s ∉ ord → (ord.foldl (augmentSet inst α OPT w') p).1 s = p.1 s) ∧
    potential inst α OPT (ord.foldl (augmentSet inst α OPT w') p).1
        (ord.foldl (augmentSet inst α OPT w') p).2 ≤ potential inst α OPT p.1 p.2 ∧
    p.2 ⊆ (ord.foldl (augmentSet inst α OPT w') p).2 := by
  induction ord with
  | nil =>
    intro p hp
    exact ⟨hp, fun s hs => by simp at hs, fun _ _ => rfl, le_rfl, subset_rfl⟩
  | cons x l ih =>
    intro p hp
    obtain ⟨a1, a2, a3, a4, a5⟩ := augmentSet_spec inst α hα OPT w' p hp x
    obtain ⟨b1, b2, b3, b4, b5⟩ := ih (augmentSet inst α OPT w' p x) a1
    simp only [List.foldl_cons]
    refine ⟨b1, ?_, ?_, le_trans b4 a4, subset_trans a5 b5⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · by_cases hsl : s ∈ l
        · exact b2 s hsl
        · rw [b3 s hsl]; exact a2
      · exact b2 s hs
    · intro s hs
      have hs1 : s ≠ x := fun h => hs (h ▸ List.mem_cons_self)
      have hs2 : s ∉ l := fun h => hs (List.mem_cons_of_mem _ h)
      rw [b3 s hs2, a3 s hs1]

lemma cov_of_pot {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ) (w : T → ℝ) (C : Finset T)
    (hΦ : potential inst α OPT w C ≤ 1) (e : E) (hw : 1 ≤ elementWeight inst w e) :
    coveredBy inst C e := by
  classical
  by_contra hcov
  have hf : fval inst α w e = 1 := by
    unfold fval
    apply min_eq_left
    apply Real.one_le_exp
    nlinarith
  have hprod : ∏ e' ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e), (1 - fval inst α w e') = 0 := by
    apply Finset.prod_eq_zero (i := e)
    · simp [hcov]
    · rw [hf]; simp
  have h1 : potential1 inst α w C = 1 := by
    unfold potential1
    rw [hprod]; simp
  have h2 : 0 < potential2 α OPT w C := Real.exp_pos _
  unfold potential at hΦ
  linarith


def SInv {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (d OPT : ℕ) (st : State T) : Prop :=
  FInv inst B d st.frac ∧
    potential inst (alphaParam (Fintype.card E) OPT) OPT st.frac.w st.cover ≤ 1

lemma step_frac {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (d OPT : ℕ) (ord : List T) (st : State T) (e : E) :
    (step inst B d OPT ord st e).frac = fracStep inst B d st.frac e := rfl

lemma step_cover {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (d OPT : ℕ) (ord : List T) (st : State T) (e : E) :
    (step inst B d OPT ord st e).cover
      = (ord.foldl (augmentSet inst (alphaParam (Fintype.card E) OPT) OPT
          (fracStep inst B d st.frac e).w) (st.frac.w, st.cover)).2 := rfl

lemma step_spec {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 1 ≤ d) (OPT : ℕ)
    (ord : List T) (hord : ∀ s, s ∈ ord) (st : State T) (hS : SInv inst B d OPT st) (e : E)
    (hne : (inst.elemSets e).Nonempty) (hcard : (inst.elemSets e).card ≤ d) :
    SInv inst B d OPT (step inst B d OPT ord st e) ∧
    st.cover ⊆ (step inst B d OPT ord st e).cover ∧
    coveredBy inst (step inst B d OPT ord st e).cover e := by
  have hα : 0 ≤ alphaParam (Fintype.card E) OPT := le_trans zero_le_one (alpha_ge_one _ _)
  obtain ⟨a1, a2, a3, -, -⟩ := frac_step_spec inst B hB d hd st.frac hS.1 e hne hcard
  obtain ⟨b1, b2, -, b4, b5⟩ := aug_fold inst _ hα OPT (fracStep inst B d st.frac e).w ord
    (st.frac.w, st.cover) a2
  have hfun : (ord.foldl (augmentSet inst (alphaParam (Fintype.card E) OPT) OPT
      (fracStep inst B d st.frac e).w) (st.frac.w, st.cover)).1
      = (fracStep inst B d st.frac e).w := funext (fun s => b2 s (hord s))
  have hpot : potential inst (alphaParam (Fintype.card E) OPT) OPT
      (fracStep inst B d st.frac e).w
      (ord.foldl (augmentSet inst (alphaParam (Fintype.card E) OPT) OPT
      (fracStep inst B d st.frac e).w) (st.frac.w, st.cover)).2 ≤ 1 := by
    rw [hfun] at b4
    exact le_trans b4 hS.2
  have hcov := cov_of_pot inst _ hα OPT _ _ hpot e a3
  refine ⟨⟨a1, ?_⟩, b5, ?_⟩
  · rw [step_frac, step_cover]; exact hpot
  · rw [step_cover]; exact hcov

lemma run_spec {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 1 ≤ d) (OPT : ℕ)
    (ord : List T) (hord : ∀ s, s ∈ ord) (σ : List E)
    (hσ : ∀ e ∈ σ, (inst.elemSets e).Nonempty ∧ (inst.elemSets e).card ≤ d) :
    ∀ st : State T, SInv inst B d OPT st →
    SInv inst B d OPT (σ.foldl (step inst B d OPT ord) st) ∧
    st.cover ⊆ (σ.foldl (step inst B d OPT ord) st).cover ∧
    (∀ e ∈ σ, coveredBy inst (σ.foldl (step inst B d OPT ord) st).cover e) ∧
    (σ.foldl (step inst B d OPT ord) st).frac = σ.foldl (fracStep inst B d) st.frac := by
  induction σ with
  | nil => intro st hst; exact ⟨hst, subset_rfl, fun e he => by simp at he, rfl⟩
  | cons x τ ih =>
    intro st hst
    have hx := hσ x List.mem_cons_self
    obtain ⟨a1, a2, a3⟩ := step_spec inst B hB d hd OPT ord hord st hst x hx.1 hx.2
    obtain ⟨b1, b2, b3, b4⟩ := ih (fun e he => hσ e (List.mem_cons_of_mem _ he))
      (step inst B d OPT ord st x) a1
    simp only [List.foldl_cons]
    refine ⟨b1, subset_trans a2 b2, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨t, ht, htC⟩ := a3
        exact ⟨t, ht, b2 htC⟩
      · exact b3 e he
    · rw [b4, step_frac]

lemma alg_core {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hc : ∀ s, inst.c s = 1)
    (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 1 ≤ d) (hfreq : ∀ e, (inst.elemSets e).card ≤ d)
    (OPT : ℕ) (hOPT : 1 ≤ OPT) (ord : List T) (hord : ∀ s, s ∈ ord) (σ : List E)
    (hopt : ∃ F : Finset T, F.card ≤ OPT ∧ ∀ e ∈ σ, coveredBy inst F e) :
    (∀ e ∈ σ, coveredBy inst (run inst B d OPT ord σ).cover e) ∧
    ((run inst B d OPT ord σ).cover.card : ℝ)
      ≤ (2 * alphaParam (Fintype.card E) OPT * Real.log (1 + (d : ℝ)) + 1) * (OPT : ℝ)
          / Real.log 2 := by
  obtain ⟨F, hFcard, hF⟩ := hopt
  have hne : ∀ e ∈ σ, (inst.elemSets e).Nonempty := by
    intro e he
    obtain ⟨t, ht, _⟩ := hF e he
    exact ⟨t, ht⟩
  have hα : 0 ≤ alphaParam (Fintype.card E) OPT := le_trans zero_le_one (alpha_ge_one _ _)
  have hS0 : SInv inst B d OPT ⟨FracState.init T, ∅⟩ :=
    ⟨FInv_init inst B d, (pot_core_i inst OPT hOPT).1⟩
  obtain ⟨c1, -, c3, c4⟩ := run_spec inst B hB d hd OPT ord hord σ
    (fun e he => ⟨hne e he, hfreq e⟩) ⟨FracState.init T, ∅⟩ hS0
  unfold run
  refine ⟨c3, ?_⟩
  set st := σ.foldl (step inst B d OPT ord) ⟨FracState.init T, ∅⟩ with hst
  have hfr : st.frac = fracRun inst B d σ := c4
  have hΦ := c1.2
  -- fractional cost bound
  set w'' : T → ℝ := fun s => if s ∈ F then 1 else 0 with hw''
  have hw''0 : ∀ s, 0 ≤ w'' s := fun s => by simp only [hw'']; split_ifs <;> norm_num
  have hw''1 : ∀ e ∈ σ, 1 ≤ elementWeight inst w'' e := by
    intro e he
    obtain ⟨t, ht, htF⟩ := hF e he
    unfold elementWeight
    calc (1:ℝ) = w'' t := by simp [hw'', htF]
      _ ≤ ∑ s ∈ inst.elemSets e, w'' s :=
        Finset.single_le_sum (f := w'') (fun s _ => hw''0 s) ht
  have hcost := (frac_core inst B hB d hd σ (fun e _ => hfreq e) hne).2 w'' hw''0 hw''1
  have hW'' : ∑ s, inst.c s * w'' s = (F.card : ℝ) := by
    simp [hc, hw'']
  have hcw : ∑ s, inst.c s * (fracRun inst B d σ).w s = ∑ s, (fracRun inst B d σ).w s := by
    simp [hc]
  rw [hcw, hW''] at hcost
  -- potential bound
  have hΦ' : potential2 (alphaParam (Fintype.card E) OPT) OPT st.frac.w st.cover ≤ 1 := by
    have h1 : 0 ≤ potential1 inst (alphaParam (Fintype.card E) OPT) st.frac.w st.cover := by
      classical
      unfold potential1
      have : ∏ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst st.cover e),
          (1 - fval inst (alphaParam (Fintype.card E) OPT) st.frac.w e) ≤ 1 :=
        Finset.prod_le_one (fun e _ => by
          have : fval inst (alphaParam (Fintype.card E) OPT) st.frac.w e ≤ 1 := min_le_left _ _
          linarith) (fun e _ => by
          have : 0 ≤ fval inst (alphaParam (Fintype.card E) OPT) st.frac.w e :=
            le_min zero_le_one (Real.exp_pos _).le
          have h2 : fval inst (alphaParam (Fintype.card E) OPT) st.frac.w e ≤ 1 := min_le_left _ _
          linarith)
      linarith
    unfold potential at hΦ
    linarith
  unfold potential2 at hΦ'
  have hsum : ∑ s, (Real.log 2 * (if s ∈ st.cover then (1:ℝ) else 0)
      - alphaParam (Fintype.card E) OPT * st.frac.w s) - (OPT : ℝ) ≤ 0 :=
    Real.exp_le_one_iff.mp hΦ'
  have hsplit : ∑ s, (Real.log 2 * (if s ∈ st.cover then (1:ℝ) else 0)
      - alphaParam (Fintype.card E) OPT * st.frac.w s)
      = Real.log 2 * (st.cover.card : ℝ) - alphaParam (Fintype.card E) OPT * ∑ s, st.frac.w s := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simp
  rw [hsplit] at hsum
  rw [hfr] at hsum
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogd : 0 ≤ Real.log (1 + (d : ℝ)) := Real.log_nonneg (by have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  have hFO : (F.card : ℝ) ≤ OPT := by exact_mod_cast hFcard
  have hW : ∑ s, (fracRun inst B d σ).w s ≤ 2 * Real.log (1 + (d : ℝ)) * OPT :=
    le_trans hcost (mul_le_mul_of_nonneg_left hFO (by positivity))
  rw [le_div_iff₀ hl2]
  have h3 := mul_le_mul_of_nonneg_left hW hα
  nlinarith


end BNCovPack.SetCover

open BNCovPack.SetCover
open OnlinePrimalDual.OnlineSetCover

theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hc : ∀ s, inst.c s = 1)
    (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 1 ≤ d) (hfreq : ∀ e, (inst.elemSets e).card ≤ d)
    (OPT : ℕ) (hOPT : 1 ≤ OPT) (ord : List T) (hord : ∀ s, s ∈ ord) (σ : List E)
    (hopt : ∃ F : Finset T, F.card ≤ OPT ∧ ∀ e ∈ σ, coveredBy inst F e) :
    (∀ e ∈ σ, coveredBy inst (run inst B d OPT ord σ).cover e) ∧
    ((run inst B d OPT ord σ).cover.card : ℝ)
      ≤ (2 * alphaParam (Fintype.card E) OPT * Real.log (1 + (d : ℝ)) + 1) * (OPT : ℝ)
          / Real.log 2 := by
  exact alg_core inst hc B hB d hd hfreq OPT hOPT ord hord σ hopt
