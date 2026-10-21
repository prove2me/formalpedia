-- Prove2me | solution 1 for DelayDep.Equiv.lemma_1_sufficiency
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:13:26.431113+00:00
-- url     : https://prove2.me/submissions/09bcb1f7-7fc2-4c6e-bc8f-49e145553012

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DDX
open MeasureTheory ProbabilityTheory Filter DelayDep.Equiv
open scoped Classical

noncomputable def cS (x : ℝ) : ℝ := max 0 (min 1 x)
noncomputable def cT (y : ℝ) : ℝ := max 5 (min 6 y)

lemma cS_nonneg (x : ℝ) : 0 ≤ cS x := le_max_left _ _
lemma cS_le (x : ℝ) : cS x ≤ 1 := max_le zero_le_one (min_le_left _ _)
lemma cT_ge (x : ℝ) : 5 ≤ cT x := le_max_left _ _
lemma cT_le (x : ℝ) : cT x ≤ 6 := max_le (by norm_num) (min_le_left _ _)

noncomputable def αc (i : ℕ) : ℝ := if i = 0 then 1 else if i = 1 then 1/2 else 100
def uc : Fin 1 → ℝ := fun _ => 2

lemma sortR_one (v : Fin 1 → ℝ) : sortR v = v := by
  unfold sortR; funext k; simp [Subsingleton.elim (Tuple.sort v) (Equiv.refl _)]

lemma e1_one : (e1 : Fin 1 → ℝ) = fun _ => 1 := by
  funext k; simp [e1, Fin.fin_one_eq_zero k]

lemma kappa0 : kappa αc 0 = 1 := by simp [kappa, αc]
lemma kappa1 : kappa αc 1 = 3/2 := by simp [kappa, αc, Finset.sum_range_succ]; norm_num
lemma kappa2 : kappa αc 2 = 203/2 := by simp [kappa, αc, Finset.sum_range_succ]; norm_num

lemma kappa_mono (i j : ℕ) (h : i ≤ j) : kappa αc i ≤ kappa αc j := by
  unfold kappa
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
  intro k _ _; simp only [αc]; split_ifs <;> norm_num

lemma nextArr50 : nextArr αc (50 : ℝ) = 2 := by
  unfold nextArr
  have h2 : (2:ℕ) ∈ {i | (50:ℝ) < kappa αc i} := by
    simp [kappa2]; norm_num
  apply le_antisymm (Nat.sInf_le h2)
  apply le_csInf ⟨2, h2⟩
  intro i hi
  simp only [Set.mem_setOf_eq, NNReal.coe_ofNat] at hi
  by_contra hlt
  push_neg at hlt
  have := kappa_mono i 1 (by omega)
  rw [kappa1] at this; linarith

lemma wait0 (tp : ℕ → ℝ) (sv : ℕ → ℝ → ℝ) : wait αc uc tp sv 0 = 1 := by
  simp [wait, Zvec, sortR_one, uc, αc]; norm_num

lemma wait1 (tp : ℕ → ℝ) (sv : ℕ → ℝ → ℝ) (htp : 1 ≤ tp 0) (c : ℝ) (hc : sv 0 1 = c)
    (hc0 : 0 ≤ c) : wait αc uc tp sv 1 = 1/2 + c := by
  simp only [wait, Zvec, sortR_one, uc, αc, e1_one]
  norm_num [htp, hc]
  rw [max_eq_left (by linarith)]; ring

lemma Y_eq (tp : ℕ → ℝ) (sv : ℕ → ℝ → ℝ) :
    (pathX αc uc tp sv (50 : NNReal)).1 =
      (if inService αc uc tp sv (50 : ℝ) 0 then 1 else 0) +
      (if inService αc uc tp sv (50 : ℝ) 1 then 1 else 0) := by
  simp only [pathX, remainingList, List.length_append, List.length_map, NNReal.coe_ofNat]
  rw [nextArr50]
  by_cases h0 : inService αc uc tp sv (50 : ℝ) 0 <;>
    by_cases h1 : inService αc uc tp sv (50 : ℝ) 1 <;>
    simp [uc, List.range_succ, List.filter_cons, h0, h1] <;>
    exact decide_eq_false (by norm_num)

end DDX

namespace DDX
open MeasureTheory ProbabilityTheory Filter DelayDep.Equiv
open scoped Classical

/-! ### Path computations -/

noncomputable def svP (x : ℕ → ℝ × ℝ) (i : ℕ) (z : ℝ) : ℝ :=
  cS (x i).1 + (if i = 1 then (if z = 1/2 + cS (x 0).1 then 100 else 0) else 0)

lemma exoY (x : ℕ → ℝ × ℝ) :
    (pathX αc uc (fun i => cT (x i).2) (fun i _ => cS (x i).1) (50 : NNReal)).1 = 0 := by
  rw [Y_eq]
  have hw1 := wait1 (fun i => cT (x i).2) (fun i _ => cS (x i).1)
    (by have := cT_ge (x 0).2; show (1:ℝ) ≤ cT (x 0).2; linarith) (cS (x 0).1) rfl (cS_nonneg _)
  have h0 : ¬ inService αc uc (fun i => cT (x i).2) (fun i _ => cS (x i).1) (50 : ℝ) 0 := by
    rintro ⟨-, -, -, h⟩
    rw [wait0, kappa0] at h
    have := cS_le (x 0).1; linarith
  have h1 : ¬ inService αc uc (fun i => cT (x i).2) (fun i _ => cS (x i).1) (50 : ℝ) 1 := by
    rintro ⟨-, -, -, h⟩
    rw [hw1, kappa1] at h
    have := cS_le (x 0).1; have := cS_le (x 1).1; linarith
  simp [h0, h1]

lemma endoY (x : ℕ → ℝ × ℝ) :
    (pathX αc uc (fun i => cT (x i).2) (svP x) (50 : NNReal)).1 = 1 := by
  rw [Y_eq]
  have hw1 := wait1 (fun i => cT (x i).2) (svP x)
    (by have := cT_ge (x 0).2; show (1:ℝ) ≤ cT (x 0).2; linarith) (cS (x 0).1) (by simp [svP]) (cS_nonneg _)
  have h0 : ¬ inService αc uc (fun i => cT (x i).2) (svP x) (50 : ℝ) 0 := by
    rintro ⟨-, -, -, h⟩
    rw [wait0, kappa0] at h
    simp [svP] at h
    have := cS_le (x 0).1; linarith
  have h1 : inService αc uc (fun i => cT (x i).2) (svP x) (50 : ℝ) 1 := by
    refine ⟨by rw [nextArr50]; norm_num, ?_, ?_, ?_⟩
    · show wait _ _ _ _ 1 ≤ cT (x 1).2
      rw [hw1]; have := cT_ge (x 1).2; have := cS_le (x 0).1; linarith
    · rw [hw1, kappa1]; have := cS_le (x 0).1; linarith
    · rw [hw1, kappa1]; simp [svP]
      have := cS_nonneg (x 0).1; have := cS_nonneg (x 1).1; linarith
  simp [h0, h1]

end DDX

namespace DDX
open MeasureTheory ProbabilityTheory Filter DelayDep.Equiv
open scoped Classical

noncomputable def ind (a b : ℝ) (x : ℝ) : ℝ := (Set.Icc a b).indicator (fun _ => (1:ℝ)) x
noncomputable def f0 (x y : ℝ) : ℝ := ind 0 1 x * ind 5 6 y

noncomputable def νS : Measure ℝ := volume.restrict (Set.Icc 0 1)
noncomputable def νT : Measure ℝ := volume.restrict (Set.Icc 5 6)
instance : IsProbabilityMeasure νS := ⟨by simp [νS]⟩
instance : IsProbabilityMeasure νT := ⟨by simp [νT]; norm_num⟩
noncomputable def μ0 : Measure (ℝ × ℝ) := νS.prod νT

lemma measurable_ind (a b : ℝ) : Measurable (ind a b) :=
  measurable_const.indicator measurableSet_Icc

lemma ofReal_ind (a b x : ℝ) :
    ENNReal.ofReal (ind a b x) = (Set.Icc a b).indicator (fun _ => (1:ENNReal)) x := by
  by_cases h : x ∈ Set.Icc a b <;> simp [ind, h]

lemma ofReal_f0 (p : ℝ × ℝ) :
    ENNReal.ofReal (f0 p.1 p.2) =
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (5:ℝ) 6).indicator (fun _ => (1:ENNReal)) p := by
  by_cases h1 : p.1 ∈ Set.Icc (0:ℝ) 1 <;> by_cases h2 : p.2 ∈ Set.Icc (5:ℝ) 6 <;>
    simp only [f0, ind, Set.indicator, Set.mem_prod, h1, h2, if_true, if_false, and_true,
      and_false, true_and, false_and] <;> norm_num

lemma jointLaw_f0 : jointLaw f0 = μ0 := by
  unfold jointLaw μ0 νS νT
  simp_rw [ofReal_f0]
  rw [withDensity_indicator (measurableSet_Icc.prod measurableSet_Icc)]
  rw [withDensity_const, one_smul, Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc)]
  rw [Set.inter_eq_left.mpr (Set.prod_mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) 1 ⊆ Set.Ici 0)
    (show Set.Icc (5:ℝ) 6 ⊆ Set.Ici 0 from fun x hx => by simp only [Set.mem_Ici]; linarith [hx.1]))]
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

instance : IsProbabilityMeasure μ0 := by unfold μ0; infer_instance

lemma isJointPdf_f0 : IsJointPdf f0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((measurable_ind 0 1).comp measurable_fst).mul ((measurable_ind 5 6).comp measurable_snd)
  · intro x y; unfold f0 ind
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ Set.univ) jointLaw_f0
    simp only [jointLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    rw [h]; exact measure_univ

lemma int_ind01 : ∫ x in Set.Ici (0:ℝ), ind 0 1 x = 1 := by
  unfold ind
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr Set.Icc_subset_Ici_self]
  simp

lemma fTex_f0 : fTex f0 = ind 5 6 := by
  funext y
  unfold fTex f0
  rw [integral_mul_const, int_ind01, one_mul]

lemma tailT_f0 (z : ℝ) : tailT f0 z = ∫ y in Set.Ioi z, ind 5 6 y := by
  unfold tailT; rw [fTex_f0]

lemma psiEn_f0 (z : ℝ) (hz : tailT f0 z ≠ 0) (x : ℝ) : psiEn f0 x z = ind 0 1 x := by
  unfold psiEn
  have : (∫ y in Set.Ioi z, f0 x y) = ind 0 1 x * tailT f0 z := by
    rw [tailT_f0]; unfold f0; rw [integral_const_mul]
  rw [this, mul_div_assoc, div_self hz, mul_one]

lemma pdfLaw_ind (a b : ℝ) (ha : 0 ≤ a) : pdfLaw (ind a b) = volume.restrict (Set.Icc a b) := by
  unfold pdfLaw
  simp_rw [ofReal_ind]
  rw [withDensity_indicator measurableSet_Icc, withDensity_const, one_smul,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (show Set.Icc a b ⊆ Set.Ici 0 from fun x hx => le_trans ha hx.1)]

end DDX

namespace DDX
open MeasureTheory ProbabilityTheory Filter DelayDep.Equiv
open scoped Classical

abbrev Ω0 := ℕ → ℝ × ℝ
noncomputable def P0 : Measure Ω0 := Measure.infinitePi (fun _ : ℕ => μ0)
instance : IsProbabilityMeasure P0 := by unfold P0; infer_instance

lemma measurable_cS : Measurable cS := by unfold cS; fun_prop
lemma measurable_cT : Measurable cT := by unfold cT; fun_prop

lemma map_eval (i : ℕ) : P0.map (fun ω => ω i) = μ0 := by
  unfold P0; exact Measure.infinitePi_map_eval _ i

lemma cS_ae : cS =ᵐ[νS] id := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp [cS, hx.1, hx.2]

lemma cT_ae : cT =ᵐ[νT] id := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp [cT, hx.1, hx.2]

lemma map_cS : νS.map cS = νS := by
  rw [Measure.map_congr cS_ae, Measure.map_id]
lemma map_cT : νT.map cT = νT := by
  rw [Measure.map_congr cT_ae, Measure.map_id]

lemma map_fst_i (i : ℕ) : P0.map (fun ω => (ω i).1) = νS := by
  have : (fun ω : Ω0 => (ω i).1) = Prod.fst ∘ (fun ω => ω i) := rfl
  rw [this, ← Measure.map_map measurable_fst (measurable_pi_apply i), map_eval]
  simp [μ0]
lemma map_snd_i (i : ℕ) : P0.map (fun ω => (ω i).2) = νT := by
  have : (fun ω : Ω0 => (ω i).2) = Prod.snd ∘ (fun ω => ω i) := rfl
  rw [this, ← Measure.map_map measurable_snd (measurable_pi_apply i), map_eval]
  simp [μ0]

lemma law_cS (i : ℕ) : P0.map (fun ω => cS (ω i).1) = νS := by
  have : (fun ω : Ω0 => cS (ω i).1) = cS ∘ (fun ω => (ω i).1) := rfl
  rw [this, ← Measure.map_map measurable_cS
    (show Measurable (fun ω : Ω0 => (ω i).1) from measurable_fst.comp (measurable_pi_apply i)),
    map_fst_i, map_cS]
lemma law_cT (i : ℕ) : P0.map (fun ω => cT (ω i).2) = νT := by
  have : (fun ω : Ω0 => cT (ω i).2) = cT ∘ (fun ω => (ω i).2) := rfl
  rw [this, ← Measure.map_map measurable_cT
    (show Measurable (fun ω : Ω0 => (ω i).2) from measurable_snd.comp (measurable_pi_apply i)),
    map_snd_i, map_cT]

lemma law_cl (i : ℕ) : P0.map (fun ω => (cS (ω i).1, cT (ω i).2)) = jointLaw f0 := by
  have : (fun ω : Ω0 => (cS (ω i).1, cT (ω i).2)) = Prod.map cS cT ∘ (fun ω => ω i) := rfl
  rw [this, ← Measure.map_map (measurable_cS.prodMap measurable_cT) (measurable_pi_apply i),
    map_eval, jointLaw_f0, μ0, ← Measure.map_prod_map _ _ measurable_cS measurable_cT,
    map_cS, map_cT]

lemma indep_snd_fst (i : ℕ) : IndepFun (fun ω : Ω0 => (ω i).2) (fun ω => (ω i).1) P0 := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (show Measurable (fun ω : Ω0 => (ω i).2) from measurable_snd.comp (measurable_pi_apply i)).aemeasurable
    (show Measurable (fun ω : Ω0 => (ω i).1) from measurable_fst.comp (measurable_pi_apply i)).aemeasurable,
    map_snd_i, map_fst_i]
  have : (fun ω : Ω0 => ((ω i).2, (ω i).1)) = Prod.swap ∘ (fun ω => ω i) := rfl
  rw [this, ← Measure.map_map measurable_swap (measurable_pi_apply i), map_eval, μ0,
    Measure.prod_swap]

/-- inputs -/
noncomputable def I0 : Inputs 1 Ω0 where
  α := fun i _ => αc i
  u := fun _ => uc
  measurable_α := fun _ => measurable_const
  measurable_u := measurable_const
  α_pos := by intro i ω; simp only [αc]; split_ifs <;> norm_num
  kappa_tendsto := by
    intro ω
    have hk : ∀ i : ℕ, ((i:ℝ) + 1) / 2 ≤ kappa αc i := by
      intro i
      unfold kappa
      have : ∀ j ∈ Finset.range (i+1), (1/2 : ℝ) ≤ αc j := by
        intro j _; simp only [αc]; split_ifs <;> norm_num
      have h := Finset.sum_le_sum this
      simp at h; linarith
    refine tendsto_atTop_mono hk ?_
    exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_div_const (by norm_num)
  u_nonneg := by intro ω k; simp [uc]

noncomputable def E0 : ExoSystem 1 f0 P0 where
  toInputs := I0
  S := fun i ω => cS (ω i).1
  T := fun i ω => cT (ω i).2
  measurable_S := fun i => measurable_cS.comp (measurable_fst.comp (measurable_pi_apply i))
  measurable_T := fun i => measurable_cT.comp (measurable_snd.comp (measurable_pi_apply i))
  law_ST := law_cl
  indep_customers := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => μ0)
      (X := fun _ (p : ℝ × ℝ) => (cS p.1, cT p.2)) (fun _ => (measurable_cS.comp measurable_fst).prodMk (measurable_cT.comp measurable_snd))
    exact this
  indep_inputs := indepFun_const_left ((fun i => αc i), uc) _

end DDX

namespace DDX
open MeasureTheory ProbabilityTheory Filter DelayDep.Equiv
open scoped Classical

def aeSig {β : Type} (X Y : Ω0 → β) : MeasurableSpace β where
  MeasurableSet' s := X ⁻¹' s =ᵐ[P0] Y ⁻¹' s
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    rw [Set.preimage_compl, Set.preimage_compl]; exact hs.compl
  measurableSet_iUnion f hf := by
    rw [Set.preimage_iUnion, Set.preimage_iUnion]; exact EventuallyEq.countable_iUnion hf

noncomputable def custP (ω : Ω0) : ℕ → ℝ × (ℝ → ℝ) := fun i => (cT (ω i).2, svP ω i)
noncomputable def custH (ω : Ω0) : ℕ → ℝ × (ℝ → ℝ) := fun i => (cT (ω i).2, fun _ => cS (ω i).1)

lemma Q1 (i : ℕ) (z : ℝ) : (fun ω : Ω0 => svP ω i z) =ᵐ[P0] (fun ω => cS (ω i).1) := by
  by_cases hi : i = 1
  · subst hi
    have hne : ∀ᵐ x ∂νS, x ≠ z - 1/2 := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      rw [νS, Measure.restrict_apply (measurableSet_singleton _)]
      exact measure_mono_null Set.inter_subset_left (measure_singleton _)
    have h2 : ∀ᵐ x ∂νS, cS x ≠ z - 1/2 := by
      filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with x hx hx2
      have : cS x = x := by simp [cS, hx2.1, hx2.2]
      rwa [this]
    rw [← map_fst_i 0] at h2
    have h3 := ae_of_ae_map
      (show Measurable (fun ω : Ω0 => (ω 0).1) from measurable_fst.comp (measurable_pi_apply 0)).aemeasurable h2
    filter_upwards [h3] with ω hω
    simp only [svP, if_true]
    rw [if_neg (by intro h; apply hω; linarith), add_zero]
  · exact Eventually.of_forall (fun ω => by simp [svP, hi])

lemma L (s : Set (ℕ → ℝ × (ℝ → ℝ))) (hs : MeasurableSet s) :
    custP ⁻¹' s =ᵐ[P0] custH ⁻¹' s := by
  have h : (inferInstance : MeasurableSpace (ℕ → ℝ × (ℝ → ℝ))) ≤ aeSig custP custH := by
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    refine sup_le ?_ ?_
    · rw [MeasurableSpace.comap_le_iff_le_map]
      intro t _
      exact EventuallyEq.rfl
    · rw [MeasurableSpace.comap_le_iff_le_map]
      refine iSup_le fun z => ?_
      rw [MeasurableSpace.comap_le_iff_le_map]
      intro t _
      show (fun ω => svP ω i z) ⁻¹' t =ᵐ[P0] (fun ω => cS (ω i).1) ⁻¹' t
      filter_upwards [Q1 i z] with ω hω
      show (svP ω i z ∈ t) = (cS (ω i).1 ∈ t)
      rw [hω]
  exact h s hs

lemma Lmeas (s : Set (ℕ → ℝ × (ℝ → ℝ))) (hs : MeasurableSet s) :
    P0 (custP ⁻¹' s) = P0 (custH ⁻¹' s) := measure_congr (L s hs)

lemma measurable_svP (i : ℕ) : Measurable (fun p : Ω0 × ℝ => svP p.1 i p.2) := by
  unfold svP
  have hS : Measurable (fun p : Ω0 × ℝ => cS (p.1 i).1) :=
    measurable_cS.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))
  have h0 : Measurable (fun p : Ω0 × ℝ => 1/2 + cS (p.1 0).1) :=
    measurable_const.add
      (measurable_cS.comp (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_fst)))
  by_cases hi : i = 1
  · subst hi
    simp only [if_true]
    exact hS.add (Measurable.ite (measurableSet_eq_fun measurable_snd h0) measurable_const
      measurable_const)
  · simp only [hi, if_false, add_zero]; exact hS

lemma honest_iIndep : iIndepFun (fun i ω => custH ω i) P0 :=
  iIndepFun_infinitePi (P := fun _ : ℕ => μ0)
    (X := fun _ (p : ℝ × ℝ) => (cT p.2, fun _ : ℝ => cS p.1))
    (fun _ => (measurable_cT.comp measurable_snd).prodMk
      (measurable_pi_lambda _ (fun _ => measurable_cS.comp measurable_fst)))

lemma pert_iIndep : iIndepFun (fun i ω => custP ω i) P0 := by
  have H := honest_iIndep
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at H ⊢
  intro S sets hsets
  have hm : MeasurableSet (⋂ i ∈ S, (fun c : ℕ → ℝ × (ℝ → ℝ) => c i) ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet (fun i hi => measurable_pi_apply i (hsets i hi))
  have e1 : (⋂ i ∈ S, (fun ω => custP ω i) ⁻¹' sets i) =
      custP ⁻¹' (⋂ i ∈ S, (fun c : ℕ → ℝ × (ℝ → ℝ) => c i) ⁻¹' sets i) := by
    ext ω; simp
  have e2 : (⋂ i ∈ S, (fun ω => custH ω i) ⁻¹' sets i) =
      custH ⁻¹' (⋂ i ∈ S, (fun c : ℕ → ℝ × (ℝ → ℝ) => c i) ⁻¹' sets i) := by
    ext ω; simp
  rw [e1, Lmeas _ hm, ← e2, H S hsets]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  exact (Lmeas _ (measurable_pi_apply i (hsets i hi))).symm

lemma honest_TS (i : ℕ) :
    IndepFun (fun ω : Ω0 => cT (ω i).2) (fun ω => fun _ : ℝ => cS (ω i).1) P0 :=
  (indep_snd_fst i).comp measurable_cT (measurable_pi_lambda _ (fun _ => measurable_cS))

lemma pert_TS (i : ℕ) : IndepFun (fun ω : Ω0 => cT (ω i).2) (fun ω => svP ω i) P0 := by
  have H := honest_TS i
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at H ⊢
  intro t1 t2 h1 h2
  have m1 : MeasurableSet {c : ℕ → ℝ × (ℝ → ℝ) | (c i).1 ∈ t1 ∧ (c i).2 ∈ t2} :=
    ((measurable_fst.comp (measurable_pi_apply i)) h1).inter
      ((measurable_snd.comp (measurable_pi_apply i)) h2)
  have m2 : MeasurableSet {c : ℕ → ℝ × (ℝ → ℝ) | (c i).2 ∈ t2} :=
    (measurable_snd.comp (measurable_pi_apply i)) h2
  have k1 := Lmeas _ m1
  have k2 := Lmeas _ m2
  exact k1.trans ((H t1 t2 h1 h2).trans (by congr 1; exact k2.symm))

noncomputable def N0 : EndoSystem 1 (fTex f0) (psiEn f0) P0 where
  toInputs := I0
  T := fun i ω => cT (ω i).2
  S := fun i ω z => svP ω i z
  measurable_T := fun i => measurable_cT.comp (measurable_snd.comp (measurable_pi_apply i))
  measurable_S := measurable_svP
  law_T := by
    intro i
    rw [law_cT, fTex_f0, pdfLaw_ind 5 6 (by norm_num)]; rfl
  law_S := by
    intro i z _ htail
    rw [Measure.map_congr (Q1 i z), law_cS]
    rw [show (fun x => psiEn f0 x z) = ind 0 1 from funext (psiEn_f0 z htail.ne'),
      pdfLaw_ind 0 1 le_rfl]; rfl
  indep_customers := pert_iIndep
  indep_TS := pert_TS
  indep_inputs := indepFun_const_left ((fun i => αc i), uc) _

end DDX

open MeasureTheory ProbabilityTheory DelayDep.Equiv DDX

namespace DDX

lemma isPdf_ind (a b : ℝ) (ha : 0 ≤ a) (hab : b = a + 1) : IsPdf (ind a b) := by
  refine ⟨measurable_ind a b, fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) _, ?_⟩
  have h := congrArg (fun μ : Measure ℝ => μ Set.univ) (pdfLaw_ind a b ha)
  simp only [pdfLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [h]; simp [hab]

noncomputable def NH : EndoSystem 1 (fTex f0) (psiEn f0) P0 where
  toInputs := I0
  T := fun i ω => cT (ω i).2
  S := fun i ω _ => cS (ω i).1
  measurable_T := fun i => measurable_cT.comp (measurable_snd.comp (measurable_pi_apply i))
  measurable_S := fun i =>
    measurable_cS.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))
  law_T := by
    intro i
    rw [law_cT, fTex_f0, pdfLaw_ind 5 6 (by norm_num)]; rfl
  law_S := by
    intro i z _ htail
    rw [law_cS]
    rw [show (fun x => psiEn f0 x z) = ind 0 1 from funext (psiEn_f0 z htail.ne'),
      pdfLaw_ind 0 1 le_rfl]; rfl
  indep_customers := honest_iIndep
  indep_TS := honest_TS
  indep_inputs := indepFun_const_left ((fun i => αc i), uc) _

end DDX

theorem solution : ¬ (∀ (fT : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ) (hfT : IsPdf fT)
    (hψ : ∀ z : ℝ, 0 ≤ z → 0 < ∫ y in Set.Ioi z, fT y → IsPdf (fun x => ψ x z))
    (n : ℕ) [NeZero n] (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (N₁ : EndoSystem n fT ψ P) (N₂ : EndoSystem n fT ψ P')
    (h_input : N₁.inputLaw P = N₂.inputLaw P'),
    AEMeasurable N₁.path P ∧ AEMeasurable N₂.path P' ∧ P.map N₁.path = P'.map N₂.path) := by
  intro H
  have hfT : IsPdf (fTex f0) := by rw [fTex_f0]; exact isPdf_ind 5 6 (by norm_num) (by norm_num)
  have hψ : ∀ z : ℝ, 0 ≤ z → 0 < ∫ y in Set.Ioi z, fTex f0 y → IsPdf (fun x => psiEn f0 x z) := by
    intro z _ htail
    rw [show (fun x => psiEn f0 x z) = ind 0 1 from funext (psiEn_f0 z htail.ne')]
    exact isPdf_ind 0 1 le_rfl (by norm_num)
  obtain ⟨hE, hN, heq⟩ := H (fTex f0) (psiEn f0) hfT hψ 1 Ω0 Ω0 P0 P0 NH N0 rfl
  have hC : MeasurableSet {x : NNReal → State 1 | (x 50).1 = 1} :=
    (measurable_fst.comp (measurable_pi_apply (50 : NNReal))) (measurableSet_singleton 1)
  have h1 : P0.map NH.path {x : NNReal → State 1 | (x 50).1 = 1} = 0 := by
    rw [Measure.map_apply_of_aemeasurable hE hC]
    have : NH.path ⁻¹' {x : NNReal → State 1 | (x 50).1 = 1} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have := exoY ω
      change (pathX αc uc (fun i => cT (ω i).2) (fun i _ => cS (ω i).1) (50 : NNReal)).1 ≠ 1
      rw [this]; norm_num
    rw [this, measure_empty]
  have h2 : P0.map N0.path {x : NNReal → State 1 | (x 50).1 = 1} = 1 := by
    rw [Measure.map_apply_of_aemeasurable hN hC]
    have : N0.path ⁻¹' {x : NNReal → State 1 | (x 50).1 = 1} = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact endoY ω
    rw [this, measure_univ]
  rw [heq, h2] at h1
  exact one_ne_zero h1
