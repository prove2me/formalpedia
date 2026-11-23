-- Prove2me | solution 1 for FlowSparsSchur.Main.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:18:27.839079+00:00
-- url     : https://prove2.me/submissions/5e5a3eea-9cf3-4bd0-854d-78260d8513b9

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing
import Definitions.Def_FlowSparsSchur_Main_Embedding

open FlowSparsSchur.Main
open Matrix

theorem solution {n m T : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    {r : Fin T → ℕ} (H : ∀ i, CGraph S (Fin (r i))) (hS : 2 ≤ S.card)
    (hG : G.IsCapCondGraph) (hH : ∀ i, (H i).IsCapCondGraph)
    (lam : Fin T → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (Emb : ∀ i, Matrix (Fin m) (Fin (r i)) ℝ)
    (hEmb : ∀ i, (G.incidence)ᵀ * Emb i = padOf S * ((H i).incidence)ᵀ * (H i).capMat)
    (q : ℝ) (hq : ∀ e, ∑ i, lam i * congOf G (Emb i) e ≤ q) :
    QEmbeds q (CGraph.combo lam H) G (fun s : S => s) (fun s : S => s.val) := by
  intro a D hD hRout
  rcases hRout with ⟨F, hRoutes, hLoad⟩
  let Fi : ∀ i : Fin T, Matrix (Fin (r i)) (Fin a) ℝ := fun i => Matrix.of fun f j => F ⟨i, f⟩ j
  let Fpart : ∀ i : Fin T, Matrix (Fin (r i)) (Fin a) ℝ :=
    fun i => Matrix.of fun f j => ((H i).cap f)⁻¹ * F ⟨i, f⟩ j
  let FG : Matrix (Fin m) (Fin a) ℝ := ∑ i : Fin T, Emb i * Fpart i
  refine ⟨FG, ?_, ?_⟩
  · unfold Routes
    have hcap_cancel : ∀ i : Fin T, (H i).capMat * Fpart i = Fi i := by
      intro i
      ext f j
      have hpos : (H i).cap f ≠ 0 := ne_of_gt ((hH i).2 f)
      rw [CGraph.capMat, Matrix.diagonal_mul]
      simp [Fpart, Fi, mul_inv_cancel_left₀ hpos]
    have hmul : (G.incidence)ᵀ * FG =
        padOf S * ∑ i : Fin T, ((H i).incidence)ᵀ * Fi i := by
      calc
        (G.incidence)ᵀ * FG
            = ∑ i : Fin T, (G.incidence)ᵀ * (Emb i * Fpart i) := by
                simp only [FG, Matrix.mul_sum]
        _ = ∑ i : Fin T, ((G.incidence)ᵀ * Emb i) * Fpart i := by
              refine Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_assoc]
        _ = ∑ i : Fin T, (padOf S * ((H i).incidence)ᵀ * (H i).capMat) * Fpart i := by
              refine Finset.sum_congr rfl fun i _ => by rw [hEmb i]
        _ = ∑ i : Fin T, padOf S * (((H i).incidence)ᵀ * ((H i).capMat * Fpart i)) := by
              refine Finset.sum_congr rfl fun i _ => by simp only [Matrix.mul_assoc]
        _ = ∑ i : Fin T, padOf S * (((H i).incidence)ᵀ * Fi i) := by
              refine Finset.sum_congr rfl fun i _ => by rw [hcap_cancel i]
        _ = padOf S * ∑ i : Fin T, ((H i).incidence)ᵀ * Fi i := by
              rw [Matrix.mul_sum]
    rw [hmul]
    have hsumF : (∑ i : Fin T, ((H i).incidence)ᵀ * Fi i) = D := by
      ext s j
      have hF := congr_fun (congr_fun hRoutes s) j
      have hid : extendDemand (fun s : S => s) D s j = D s j := by
        simp [extendDemand]
      rw [hid] at hF
      calc
        (∑ i : Fin T, ((H i).incidence)ᵀ * Fi i) s j
            = ∑ i : Fin T, ∑ f : Fin (r i), (H i).incidence f s * F ⟨i, f⟩ j := by
                rw [Matrix.sum_apply]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Matrix.mul_apply]
                rfl
        _ = ∑ x : Σ i, Fin (r i), (CGraph.combo lam H).incidence x s * F x j := by
              rw [Fintype.sum_sigma]
              rfl
        _ = (((CGraph.combo lam H).incidence)ᵀ * F) s j := rfl
        _ = D s j := hF
    rw [hsumF]
    ext v j
    simp only [Matrix.mul_apply, padOf, extendDemand]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hvs : v = s.val
    · subst hvs; simp
    · have hsv : s.val ≠ v := Ne.symm hvs
      simp [hvs, hsv]
  · intro e
    have hGcap_pos : 0 < G.cap e := hG.2 e
    have hentry : ∀ j : Fin a, |FG e j| ≤
        ∑ i : Fin T, ∑ f : Fin (r i), |Emb i e f| * ((H i).cap f)⁻¹ * |F ⟨i, f⟩ j| := by
      intro j
      have hFG : FG e j = ∑ i : Fin T, ∑ f : Fin (r i),
          Emb i e f * (((H i).cap f)⁻¹ * F ⟨i, f⟩ j) := by
        dsimp only [FG]
        rw [Matrix.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_apply]
        rfl
      rw [hFG]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun i _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun f _ => ?_
      have hpos : 0 ≤ ((H i).cap f)⁻¹ := inv_nonneg.mpr (le_of_lt ((hH i).2 f))
      rw [abs_mul, abs_mul, abs_of_nonneg hpos, mul_assoc]
    calc
      load FG e = ∑ j : Fin a, |FG e j| := rfl
      _ ≤ ∑ j : Fin a, ∑ i : Fin T, ∑ f : Fin (r i),
            |Emb i e f| * ((H i).cap f)⁻¹ * |F ⟨i, f⟩ j| :=
          Finset.sum_le_sum fun j _ => hentry j
      _ = ∑ i : Fin T, ∑ f : Fin (r i),
            |Emb i e f| * ((H i).cap f)⁻¹ * load F ⟨i, f⟩ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [← Finset.mul_sum]
          rfl
      _ ≤ ∑ i : Fin T, ∑ f : Fin (r i),
            |Emb i e f| * ((H i).cap f)⁻¹ * (1 * (CGraph.combo lam H).cap ⟨i, f⟩) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun f _ => ?_
          have hnn : 0 ≤ |Emb i e f| * ((H i).cap f)⁻¹ :=
            mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (le_of_lt ((hH i).2 f)))
          exact mul_le_mul_of_nonneg_left (hLoad ⟨i, f⟩) hnn
      _ = ∑ i : Fin T, lam i * (∑ f : Fin (r i), |Emb i e f|) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          have hne : (H i).cap f ≠ 0 := ne_of_gt ((hH i).2 f)
          simp only [CGraph.combo, one_mul]
          field_simp [hne]
      _ = (∑ i : Fin T, lam i * congOf G (Emb i) e) * G.cap e := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hne : G.cap e ≠ 0 := ne_of_gt hGcap_pos
          simp only [congOf]
          field_simp [hne]
      _ ≤ q * G.cap e :=
          mul_le_mul_of_nonneg_right (hq e) (le_of_lt hGcap_pos)
