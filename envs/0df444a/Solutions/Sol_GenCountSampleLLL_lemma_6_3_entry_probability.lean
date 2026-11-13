-- Prove2me | solution 1 for GenCountSampleLLL.lemma_6_3_entry_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:21:04.880067+00:00
-- url     : https://prove2.me/submissions/2b29769c-ddbf-4f17-a74e-01870ebbbfbe

import Definitions.Def_GenCountSampleLLL_twoTrees
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

private theorem piLaw_rectangle {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)]
    (μ : ∀ i, PMF (κ i)) (S : ∀ i, Finset (κ i)) :
    (∑ x : (∀ i, κ i), ((piLaw μ) x).toReal *
      (if ∀ i, x i ∈ S i then (1 : ℝ) else 0)) =
      ∏ i, ∑ y ∈ S i, (μ i y).toReal := by
  have hx (x : ∀ i, κ i) : ((piLaw μ) x).toReal = ∏ i, (μ i (x i)).toReal := by
    simp only [piLaw, PMF.ofFintype_apply, ENNReal.toReal_prod]
  calc
    _ = ∑ x : (∀ i, κ i), ∏ i, if x i ∈ S i then (μ i (x i)).toReal else 0 := by
      apply Finset.sum_congr rfl
      intro x hx'
      rw [hx]
      by_cases hp : ∀ i, x i ∈ S i
      · simp [hp]
      · simp only [hp, if_false, mul_zero]
        push Not at hp
        obtain ⟨i, hi⟩ := hp
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
    _ = ∏ i, ∑ y : κ i, if y ∈ S i then (μ i y).toReal else 0 :=
      (Fintype.prod_sum (fun i y => if y ∈ S i then (μ i y).toReal else 0)).symm
    _ = _ := by simp

private theorem prodLaw_restr_probability (I : Inst) (U : Finset (Fin I.n)) (z : I.Assign)
    (hz : z = I.restr U z) :
    (∑ σ : I.Assign, (I.prodLaw σ).toReal *
      (if I.restr U σ = z then (1 : ℝ) else 0)) = I.nuU U z := by
  classical
  let S : ∀ v : Fin I.n, Finset (Fin (I.q v)) :=
    fun v => if v ∈ U then {z v} else Finset.univ
  have hpred (σ : I.Assign) : (I.restr U σ = z) ↔ ∀ v, σ v ∈ S v := by
    constructor
    · intro he v
      by_cases hv : v ∈ U
      · have hval := congrFun he v
        simpa [S, hv, Inst.restr] using hval
      · simp [S, hv]
    · intro he
      funext v
      by_cases hv : v ∈ U
      · have hval := he v
        simpa [S, hv, Inst.restr] using hval
      · have hval := congrFun hz v
        simpa [Inst.restr, hv] using hval.symm
  have hsum (v : Fin I.n) : ∑ y : Fin (I.q v), (I.ν v y).toReal = 1 := by
    rw [← ENNReal.toReal_sum (by intro y hy; exact (I.ν v).apply_ne_top y)]
    have hfull := (I.ν v).tsum_coe
    rw [tsum_fintype] at hfull
    rw [hfull]
    simp
  have hp : (∑ σ : I.Assign, (I.prodLaw σ).toReal *
      (if ∀ v, σ v ∈ S v then (1 : ℝ) else 0)) =
      ∏ v, ∑ y ∈ S v, (I.ν v y).toReal := by
    convert piLaw_rectangle I.ν S using 1
    apply Finset.sum_congr
    · ext σ; simp
    · intro σ hσ
      by_cases hh : ∀ v, σ v ∈ S v <;> simp [hh, Inst.prodLaw]
  simp_rw [← hpred] at hp
  rw [hp]
  have hfactor (v : Fin I.n) : (∑ y ∈ S v, (I.ν v y).toReal) =
      if v ∈ U then (I.ν v (z v)).toReal else 1 := by
    by_cases hv : v ∈ U <;> simp [S, hv, hsum]
  simp_rw [hfactor]
  unfold Inst.nuU
  rw [← Finset.prod_filter]
  simp

private theorem assembled_coordinate_probability (I : Inst) (J : Type) [Fintype J]
    (U : Finset (Fin I.n)) (z : I.Assign) (h : Fin I.n → J) :
    (∑ ω : J → I.Assign, ((piLaw fun _ : J => I.prodLaw) ω).toReal *
      (if ∀ v ∈ U, ω (h v) v = z v then (1 : ℝ) else 0)) = I.nuU U z := by
  classical
  let Uj (j : J) : Finset (Fin I.n) := U.filter fun v => h v = j
  let S (j : J) : Finset I.Assign := Finset.univ.filter fun σ =>
    I.restr (Uj j) σ = I.restr (Uj j) z
  have hevent (ω : J → I.Assign) :
      (∀ v ∈ U, ω (h v) v = z v) ↔ ∀ j, ω j ∈ S j := by
    constructor
    · intro he j
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      funext v
      by_cases hv : v ∈ Uj j
      · have hv' := Finset.mem_filter.mp hv
        have hval := he v hv'.1
        rw [hv'.2] at hval
        simpa [Inst.restr, hv] using hval
      · simp [Inst.restr, hv]
    · intro he v hv
      have hj := (Finset.mem_filter.mp (he (h v))).2
      have hcoord := congrFun hj v
      have hv' : v ∈ Uj (h v) := by simp [Uj, hv]
      simpa [Inst.restr, hv'] using hcoord
  have hfactor (j : J) : (∑ σ ∈ S j, (I.prodLaw σ).toReal) = I.nuU (Uj j) z := by
    have hnorm : I.restr (Uj j) z = I.restr (Uj j) (I.restr (Uj j) z) := by
      funext v
      by_cases hv : v ∈ Uj j <;> simp [Inst.restr, hv]
    have hp := prodLaw_restr_probability I (Uj j) (I.restr (Uj j) z) hnorm
    have hnu : I.nuU (Uj j) (I.restr (Uj j) z) = I.nuU (Uj j) z := by
      unfold Inst.nuU
      apply Finset.prod_congr rfl
      intro v hv
      simp [Inst.restr, hv]
    rw [hnu] at hp
    rw [← hp]
    simp [S, Finset.sum_filter]
  have hrect := piLaw_rectangle (fun _ : J => I.prodLaw) S
  simp_rw [← hevent] at hrect
  rw [hrect]
  simp_rw [hfactor]
  unfold Inst.nuU Uj
  exact Finset.prod_fiberwise U h (fun v => (I.ν v (z v)).toReal)


private theorem pinned_sigT (I : Inst) (D T : Finset (Fin I.m)) (z : I.Assign)
    (hz : z = I.restr (I.UT D T) z) (ω : I.ExpSpace) :
    I.sigT D T (I.pin (T,z) ω) = z := by
  calc
    _ = I.restr (I.UT D T) z := by
      apply funext
      intro v
      unfold Inst.sigT Inst.restr
      by_cases hv : v ∈ I.UT D T
      · simp only [hv]
        by_cases ht : ∃ t, t ∈ T ∧ v ∈ I.vbl t
        · simp only [ht, ↓reduceDIte, Inst.pin]
          simp [(Classical.choose_spec ht).1]
        · simp [ht, Inst.pin]
      · simp [hv]
    _ = z := hz.symm

private theorem pinned_entry_present (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) (ω : I.ExpSpace) :
    (T,z) ∈ I.Le D a (T,z) ω := by
  have hzE : z ∈ I.ET D a T := (Finset.mem_filter.mp hz).1
  have hzR : z = I.restr (I.UT D T) z := (Finset.mem_filter.mp hz).2
  have hs : I.sigT D T (I.pin (T,z) ω) = z := pinned_sigT I D T z hzR ω
  unfold Inst.Le Inst.Llist
  apply Finset.mem_image.mpr
  refine ⟨T, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨hT, ?_⟩
    rw [hs]
    exact (Finset.mem_filter.mp hzE).2
  · simp [hs]

private theorem entry_mem_iff (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign) (ω : I.ExpSpace) :
    (T,z) ∈ I.Llist D a ω ↔
      T ∈ I.twoTrees D a ∧ I.inET D a T (I.sigT D T ω) ∧ I.sigT D T ω = z := by
  unfold Inst.Llist
  constructor
  · intro he
    obtain ⟨S, hS, hpair⟩ := Finset.mem_image.mp he
    have hST : S = T := congrArg Prod.fst hpair
    subst S
    refine ⟨(Finset.mem_filter.mp hS).1, (Finset.mem_filter.mp hS).2, ?_⟩
    exact congrArg Prod.snd hpair
  · rintro ⟨hT, hET, heq⟩
    apply Finset.mem_image.mpr
    exact ⟨T, Finset.mem_filter.mpr ⟨hT, hET⟩, by simp [heq]⟩

private theorem valid_entry_mem_iff_sigT (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign) (ω : I.ExpSpace)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (T,z) ∈ I.Llist D a ω ↔ I.sigT D T ω = z := by
  rw [entry_mem_iff]
  constructor
  · exact fun h => h.2.2
  · intro heq
    refine ⟨hT, ?_, heq⟩
    rw [heq]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2

private theorem nuU_positive (I : Inst) (U : Finset (Fin I.n)) (z : I.Assign) :
    0 < I.nuU U z := by
  unfold Inst.nuU
  apply Finset.prod_pos
  intro v hv
  exact ENNReal.toReal_pos (I.ν_pos v (z v)) ((I.ν v).apply_ne_top (z v))

private theorem lemma_6_3_pin_support (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∀ ω : I.ExpSpace, ((T,z) ∈ I.Llist D a ω ↔ I.sigT D T ω = z) ∧
      (T,z) ∈ I.Le D a (T,z) ω) ∧ 0 < I.nuU (I.UT D T) z := by
  exact ⟨fun ω => ⟨valid_entry_mem_iff_sigT I D a T z ω hT hz,
    pinned_entry_present I D a T z hT hz ω⟩, nuU_positive I _ z⟩



private theorem sigT_probability (I : Inst) (D T : Finset (Fin I.m)) (z : I.Assign)
    (hz : z = I.restr (I.UT D T) z) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if I.sigT D T ω = z then (1 : ℝ) else 0)) = I.nuU (I.UT D T) z := by
  let h : Fin I.n → Fin I.m ⊕ Finset (Fin I.m) := fun v =>
    if hv : ∃ t, t ∈ T ∧ v ∈ I.vbl t then Sum.inl hv.choose else Sum.inr T
  have hevent (ω : I.ExpSpace) :
      (I.sigT D T ω = z) ↔ ∀ v ∈ I.UT D T, ω (h v) v = z v := by
    constructor
    · intro he v hv
      have hc := congrFun he v
      by_cases hh : ∃ t, t ∈ T ∧ v ∈ I.vbl t <;>
        simpa [Inst.sigT, Inst.restr, h, hv, hh] using hc
    · intro he
      funext v
      by_cases hv : v ∈ I.UT D T
      · have hc := he v hv
        by_cases hh : ∃ t, t ∈ T ∧ v ∈ I.vbl t <;>
          simpa [Inst.sigT, Inst.restr, h, hv, hh] using hc
      · have hc := congrFun hz v
        simpa [Inst.sigT, Inst.restr, hv] using hc.symm
  have hp := assembled_coordinate_probability I (Fin I.m ⊕ Finset (Fin I.m)) (I.UT D T) z h
  simp_rw [← hevent] at hp
  convert hp using 1
  apply Finset.sum_congr
  · ext ω; simp
  · intro ω hω
    by_cases hs : I.sigT D T ω = z <;> simp [hs, Inst.expLaw]

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if (T,z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) = I.nuU (I.UT D T) z := by
  simp_rw [valid_entry_mem_iff_sigT I D a T z _ hT hz]
  exact sigT_probability I D T z (Finset.mem_filter.mp hz).2

