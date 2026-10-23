-- Prove2me | solution 1 for CarlssonPartition.Equitable.district_workload
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:45:48.805993+00:00
-- url     : https://prove2.me/submissions/d56bc09b-1003-4559-a327-b3abf4223fa9

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

set_option autoImplicit false
open Filter Topology MeasureTheory CarlssonPartition.Equitable

namespace CarlssonCE

noncomputable def φ : Plane →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
def Rg : Set Plane := Metric.closedBall 0 1
def R1 : Set Plane := Rg ∩ {x | φ x ≤ 0}
def R2 : Set Plane := Rg ∩ {x | 0 ≤ φ x}

lemma neg_pre : Neg.neg ⁻¹' R1 = R2 := by
  ext x; simp [R1, R2, Rg, map_neg]

lemma mR : MeasurableSet Rg := measurableSet_closedBall
lemma mR1 : MeasurableSet R1 := mR.inter (measurableSet_le φ.measurable measurable_const)
lemma mR2 : MeasurableSet R2 := mR.inter (measurableSet_le measurable_const φ.measurable)

lemma null_inter : AEDisjoint volume R1 R2 := by
  unfold AEDisjoint
  apply measure_mono_null (t := ((LinearMap.ker (φ : Plane →ₗ[ℝ] ℝ) : Submodule ℝ Plane) : Set Plane))
  · intro x hx
    simp only [R1, R2, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    linarith [hx.1.2, hx.2.2]
  · apply Measure.addHaar_submodule
    intro h
    have : (EuclideanSpace.single 0 1 : Plane) ∈ LinearMap.ker (φ : Plane →ₗ[ℝ] ℝ) := h ▸ Submodule.mem_top
    simp [φ] at this

lemma union : R1 ∪ R2 = Rg := by
  ext x; simp only [R1, R2, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h; rcases le_total (φ x) 0 with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩

lemma cR : IsCompact Rg := isCompact_closedBall 0 1

lemma sym (g : Plane → ℝ) (hg : ∀ x, g (-x) = g x) (hc : Continuous g) :
    (∫ x in R1, g x) = (1/2) * ∫ x in Rg, g x ∧ (∫ x in R2, g x) = (1/2) * ∫ x in Rg, g x := by
  have e : (∫ x in R2, g x) = ∫ x in R1, g x := by
    rw [← neg_pre]
    have := (Measure.measurePreserving_neg (volume : Measure Plane)).setIntegral_preimage_emb
      (Homeomorph.neg Plane).measurableEmbedding g R1
    simpa [hg] using this
  have hint : IntegrableOn g Rg := hc.continuousOn.integrableOn_compact cR
  have u : (∫ x in Rg, g x) = (∫ x in R1, g x) + ∫ x in R2, g x := by
    rw [← union]
    exact setIntegral_union₀ null_inter mR2.nullMeasurableSet
      (hint.mono_set (union ▸ Set.subset_union_left)) (hint.mono_set (union ▸ Set.subset_union_right))
  constructor <;> linarith

noncomputable def V : ℝ := volume.real Rg

lemma Vpos : 0 < V := by
  unfold V
  rw [measureReal_def]
  exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume 0 one_pos).ne'
    measure_closedBall_lt_top.ne

noncomputable def I : Instance :=
  { R := Rg, x0 := 0, f := fun _ => 1 / V, m := 2, v := 1, q := 2, sbar := 1, beta := 1 }

lemma intconst (S : Set Plane) (c : ℝ) : (∫ _x in S, c) = volume.real S * c := by
  rw [setIntegral_const, smul_eq_mul]

lemma std : I.Standing := by
  refine ⟨cR, convex_closedBall 0 1, Metric.mem_closedBall_self zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; show (0:ℝ) ≤ 1 / V; exact (one_div_pos.mpr Vpos).le
  · exact ⟨0, (LipschitzWith.const (1 / V)).lipschitzOnWith⟩
  · show (∫ _x in Rg, (1 / V)) = 1
    rw [intconst]; change V * (1 / V) = 1; field_simp [Vpos.ne']
  · show (1:ℕ) ≤ 2; norm_num
  · show (0:ℝ) < 1; norm_num
  · show (1:ℕ) ≤ 2; norm_num
  · show (0:ℝ) ≤ 1; norm_num
  · show (0:ℝ) < 1; norm_num

def Good (S : Set Plane) : Prop :=
  S ⊆ Rg ∧ MeasurableSet S ∧
    ∀ g : Plane → ℝ, (∀ x, g (-x) = g x) → Continuous g → (∫ x in S, g x) = (1/2) * ∫ x in Rg, g x

lemma good1 : Good R1 := ⟨Set.inter_subset_left, mR1, fun g hg hc => (sym g hg hc).1⟩
lemma good2 : Good R2 := ⟨Set.inter_subset_left, mR2, fun g hg hc => (sym g hg hc).2⟩

noncomputable def J : ℝ := ∫ x in Rg, ‖x - 0‖ * (1 / V)

lemma J_nonneg : 0 ≤ J := setIntegral_nonneg mR (fun x _ => by have := Vpos; positivity)

lemma pr_good (S : Set Plane) (hS : Good S) : I.pr S = 1 / 2 := by
  show (∫ _x in S, (1 / V)) = 1 / 2
  rw [hS.2.2 (fun _ => 1 / V) (fun _ => rfl) continuous_const, intconst]
  change 1 / 2 * (V * (1 / V)) = 1 / 2
  field_simp [Vpos.ne']

lemma W2 (lam : ℝ) : I.workload I.m lam I.R I.f = lam * ((1 + J) / 2) := by
  show lam * 1 / ((2:ℕ):ℝ) + 2 * lam * (∫ x in Rg, ‖x - 0‖ * (1 / V)) / (((2:ℕ):ℝ) * 1 * ((2:ℕ):ℝ))
    = lam * ((1 + J) / 2)
  rw [← J]; push_cast; ring

lemma W1 (S : Set Plane) (hS : Good S) (lam : ℝ) :
    I.workload 1 lam S (I.fSub S) = lam * (1 + J) := by
  have hp := pr_good S hS
  have hint : (∫ x in S, ‖x - I.x0‖ * I.fSub S x) = J := by
    show (∫ x in S, ‖x - 0‖ * ((1 / V) / I.pr S)) = J
    rw [hp]
    have : (fun x : Plane => ‖x - 0‖ * ((1 / V) / (1 / 2))) = fun x => (‖x - 0‖ * (1 / V)) * 2 := by
      funext x; ring
    rw [this, integral_mul_const, hS.2.2 _ (fun x => by simp [norm_neg]) (by fun_prop)]
    rw [← J]; ring
  unfold Instance.workload
  rw [hint]
  show lam * 1 / ((1:ℕ):ℝ) + 2 * lam * J / (((1:ℕ):ℝ) * 1 * ((2:ℕ):ℝ)) = lam * (1 + J)
  push_cast; ring

lemma S_pos : 0 < ∫ x in I.R, Real.sqrt (I.f x) := by
  show 0 < ∫ _x in Rg, Real.sqrt (1 / V)
  rw [intconst]
  have := Vpos
  exact mul_pos this (Real.sqrt_pos.mpr (by positivity))

lemma Si_pos (S : Set Plane) (hS : Good S) : 0 < ∫ x in S, Real.sqrt (I.fSub S x) := by
  show 0 < ∫ _x in S, Real.sqrt ((1 / V) / I.pr S)
  rw [pr_good S hS, hS.2.2 (fun _ => Real.sqrt ((1 / V) / (1 / 2))) (fun _ => rfl) continuous_const,
    intconst]
  have := Vpos
  have : 0 < Real.sqrt ((1 / V) / (1 / 2)) := Real.sqrt_pos.mpr (by positivity)
  change 0 < 1 / 2 * (V * _)
  positivity

lemma L2_ne (lam : ℝ) (h0 : lam ≠ 0) (h1 : lam * ((1 + J) / 2) ≠ 1) :
    I.bvrLeading I.m lam I.R I.f ≠ 0 := by
  have hS := S_pos
  unfold Instance.bvrLeading
  rw [W2]
  have : (1 : ℝ) - lam * ((1 + J) / 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  show (1:ℝ) ^ 2 * lam * (1 - 1 / ((2:ℕ):ℝ)) ^ 2 * (∫ x in I.R, Real.sqrt (I.f x)) ^ 2 /
    (2 * ((2:ℕ):ℝ) ^ 2 * 1 ^ 2 * (1 - lam * ((1 + J) / 2)) ^ 2) ≠ 0
  push_cast
  have := hS.ne'
  positivity

lemma L1_ne (S : Set Plane) (hS : Good S) (lam : ℝ) (h0 : lam ≠ 0) (h1 : lam * (1 + J) / 2 ≠ 1) :
    I.bvrLeading 1 (I.lamSub lam S) S (I.fSub S) ≠ 0 := by
  have hSi := Si_pos S hS
  have hp := pr_good S hS
  unfold Instance.bvrLeading
  rw [W1 S hS]
  unfold Instance.lamSub
  rw [hp]
  have : (1 : ℝ) - lam * (1 / 2) * (1 + J) ≠ 0 := by
    intro h; apply h1; linarith
  show (1:ℝ) ^ 2 * (lam * (1 / 2)) * (1 - 1 / ((2:ℕ):ℝ)) ^ 2 * (∫ x in S, Real.sqrt (I.fSub S x)) ^ 2 /
    (2 * ((1:ℕ):ℝ) ^ 2 * 1 ^ 2 * (1 - lam * (1 / 2) * (1 + J)) ^ 2) ≠ 0
  push_cast
  have := hSi.ne'
  positivity

noncomputable def Rs : Fin 2 → Set Plane := ![R1, R2]

lemma goodRs (i : Fin 2) : Good (Rs i) := by
  fin_cases i
  · exact good1
  · exact good2


lemma hF : I.heavy I.m I.R I.f = comap (fun lam => lam * ((1 + J) / 2)) (𝓝[<] 1) := by
  unfold Instance.heavy
  congr 1
  funext lam
  exact W2 lam

lemma hG (S : Set Plane) (hS : Good S) :
    I.heavy 1 S (I.fSub S) = comap (fun lam => lam * (1 + J)) (𝓝[<] 1) := by
  unfold Instance.heavy
  congr 1
  funext lam
  exact W1 _ hS lam

lemma evF : ∀ᶠ lam in I.heavy I.m I.R I.f, 3/4 < lam * ((1 + J) / 2) ∧ lam * ((1 + J) / 2) < 1 := by
  rw [hF]
  exact (Filter.eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (3/4:ℝ) < 1)) (fun y hy => hy)).comap _

lemma evG (S : Set Plane) (hS : Good S) :
    ∀ᶠ lam in I.heavy 1 S (I.fSub S), 1/2 < lam * (1 + J) ∧ lam * (1 + J) < 1 := by
  rw [hG S hS]
  exact (Filter.eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (1/2:ℝ) < 1)) (fun y hy => hy)).comap _

lemma neF : (I.heavy I.m I.R I.f).NeBot := by
  have : (0:ℝ) < 1 + J := by have := J_nonneg; linarith
  rw [hF]
  refine NeBot.comap_of_surj inferInstance ?_
  intro y
  exact ⟨y / ((1 + J) / 2), by field_simp⟩

lemma hP : I.IsPartition Rs := by
  refine ⟨fun i => (goodRs i).2.1.nullMeasurableSet, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact null_inter
    · exact null_inter.symm
    · exact absurd rfl hij
  · show (⋃ i, Rs i) = Rg
    rw [← union]
    ext x
    simp [Rs, Fin.exists_fin_two]

lemma h1 : ∀ i : Fin 2, (∫ x in Rs i, Real.sqrt (I.f x)) = (1 / (I.m : ℝ)) * ∫ x in I.R, Real.sqrt (I.f x) := by
  intro i
  rw [(goodRs i).2.2 _ (fun _ => rfl) (by fun_prop)]
  rfl

lemma h2 : ∀ i : Fin 2, (∫ x in Rs i, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    = (1 / (I.m : ℝ)) * ∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x := by
  intro i
  rw [(goodRs i).2.2 _ (fun x => by simp [I, norm_neg]) (by fun_prop)]
  rfl

end CarlssonCE

open CarlssonCE in
theorem solution : ¬ (∀ (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs) (i : Fin I.m)
    (h2 : (∫ x in Rs i, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = (1 / (I.m : ℝ)) * ∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (hpos : 0 < I.pr (Rs i)),
    (∀ lam : ℝ, I.workload 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i))
      = lam * (∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
          / ((I.m : ℝ) * I.v * (I.q : ℝ))) ∧
    (∀ lam : ℝ, I.workload 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i))
      = I.workload I.m lam I.R I.f) ∧
    I.heavy 1 (Rs i) (I.fSub (Rs i)) = I.heavy I.m I.R I.f) := by
  intro H
  have hpos : 0 < I.pr (Rs 0) := by rw [pr_good _ (goodRs 0)]; norm_num
  have key := (H I std Rs hP (0 : Fin 2) (h2 0) hpos).2.2
  have e1 := evF
  have e2 := evG (Rs 0) (goodRs 0)
  rw [key] at e2
  haveI := neF
  obtain ⟨lam, ha, hb⟩ := (e1.and e2).exists
  nlinarith [ha.1, hb.2]
