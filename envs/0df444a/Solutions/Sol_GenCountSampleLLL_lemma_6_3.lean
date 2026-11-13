-- Prove2me | solution 1 for GenCountSampleLLL.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:32:13.192123+00:00
-- url     : https://prove2.me/submissions/a43d2cfc-fc27-4fdb-a622-328bced44d08

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

private theorem piLaw_pin_mass {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)]
    (μ : ∀ i, PMF (κ i)) (K : Finset ι) (z y : ∀ i, κ i)
    (hy : ∀ i ∈ K, y i = z i) :
    (∏ i ∈ K, (μ i (z i)).toReal) *
      (∑ x : (∀ i, κ i), ((piLaw μ) x).toReal *
        (if (fun i => if i ∈ K then z i else x i) = y then (1 : ℝ) else 0)) =
      ((piLaw μ) y).toReal := by
  classical
  let S : ∀ i, Finset (κ i) := fun i => if i ∈ K then Finset.univ else {y i}
  have hpred (x : ∀ i, κ i) :
      ((fun i => if i ∈ K then z i else x i) = y) ↔ ∀ i, x i ∈ S i := by
    constructor
    · intro he i
      by_cases hi : i ∈ K
      · simp [S, hi]
      · have hv := congrFun he i
        simpa [S, hi] using hv
    · intro he
      funext i
      by_cases hi : i ∈ K
      · simpa [hi] using (hy i hi).symm
      · have hv := he i
        simpa [S, hi] using hv
  have hsum (i : ι) : ∑ a : κ i, (μ i a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (by intro a ha; exact (μ i).apply_ne_top a)]
    have h := (μ i).tsum_coe
    rw [tsum_fintype] at h
    rw [h]
    simp
  have hfactor (i : ι) : (∑ a ∈ S i, (μ i a).toReal) =
      if i ∈ K then 1 else (μ i (y i)).toReal := by
    by_cases hi : i ∈ K <;> simp [S, hi, hsum]
  have hp := piLaw_rectangle μ S
  simp_rw [← hpred] at hp
  rw [hp]
  simp_rw [hfactor]
  have hprod : (∏ i : ι, if i ∈ K then (1 : ℝ) else (μ i (y i)).toReal) =
      ∏ i ∈ Finset.univ.filter (fun i => i ∉ K), (μ i (y i)).toReal := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : i ∈ K <;> simp [h]
  rw [hprod]
  have hk : (∏ i ∈ K, (μ i (z i)).toReal) = ∏ i ∈ K, (μ i (y i)).toReal := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hy i hi]
  rw [hk]
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ K)
    (fun i => (μ i (y i)).toReal)
  simpa [piLaw, PMF.ofFintype_apply, ENNReal.toReal_prod] using hsplit

private theorem piLaw_pinning_expectation {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)]
    (μ : ∀ i, PMF (κ i)) (K : Finset ι) (z : ∀ i, κ i) (F : (∀ i, κ i) → ℝ) :
    (∏ i ∈ K, (μ i (z i)).toReal) *
      (∑ x : (∀ i, κ i), ((piLaw μ) x).toReal *
        F (fun i => if i ∈ K then z i else x i)) =
    ∑ y : (∀ i, κ i), ((piLaw μ) y).toReal *
      (if ∀ i ∈ K, y i = z i then F y else 0) := by
  classical
  let q : ℝ := ∏ i ∈ K, (μ i (z i)).toReal
  let pin (x : ∀ i, κ i) : ∀ i, κ i := fun i => if i ∈ K then z i else x i
  have hkernel (y : ∀ i, κ i) :
      q * (∑ x : (∀ i, κ i), ((piLaw μ) x).toReal *
        (if pin x = y then (1 : ℝ) else 0)) =
      if ∀ i ∈ K, y i = z i then ((piLaw μ) y).toReal else 0 := by
    by_cases hy : ∀ i ∈ K, y i = z i
    · rw [if_pos hy]
      exact piLaw_pin_mass μ K z y hy
    · have hn (x : ∀ i, κ i) : pin x ≠ y := by
        intro hxy
        apply hy
        intro i hi
        have := congrFun hxy i
        simpa [pin, hi] using this.symm
      simp [hy, hn]
  calc
    _ = ∑ y : (∀ i, κ i), q *
        ((∑ x : (∀ i, κ i), ((piLaw μ) x).toReal *
          (if pin x = y then (1 : ℝ) else 0)) * F y) := by
      simp only [q, pin]
      rw [← Finset.mul_sum]
      apply congrArg
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← mul_assoc, hkernel]
      by_cases h : ∀ i ∈ K, y i = z i <;> simp [h]

set_option maxHeartbeats 1600000 in
private theorem assembled_pinning_expectation (I : Inst) (J : Type) [Fintype J]
    (U : Finset (Fin I.n)) (z : I.Assign) (h : Fin I.n → J)
    (F : (J → I.Assign) → ℝ) :
    I.nuU U z *
      (∑ ω : J → I.Assign, ((piLaw fun _ : J => I.prodLaw) ω).toReal *
        F (fun j v => if v ∈ U ∧ h v = j then z v else ω j v)) =
      ∑ ω : J → I.Assign, ((piLaw fun _ : J => I.prodLaw) ω).toReal *
        (if ∀ v ∈ U, ω (h v) v = z v then F ω else 0) := by
  classical
  let E : ((p : Σ _ : J, Fin I.n) → Fin (I.q p.2)) ≃ (J → I.Assign) :=
    Equiv.piCurry (fun (_ : J) v => Fin (I.q v))
  let μ : ∀ p : Σ _ : J, Fin I.n, PMF (Fin (I.q p.2)) := fun p => I.ν p.2
  let K : Finset (Σ _ : J, Fin I.n) := U.image fun v => ⟨h v, v⟩
  let Z : (p : Σ _ : J, Fin I.n) → Fin (I.q p.2) := fun p => z p.2
  have hweight (x : (p : Σ _ : J, Fin I.n) → Fin (I.q p.2)) :
      ((piLaw μ) x).toReal = ((piLaw fun _ : J => I.prodLaw) (E x)).toReal := by
    simp only [piLaw, PMF.ofFintype_apply, ENNReal.toReal_prod, Inst.prodLaw]
    rw [Fintype.prod_sigma]
    rfl
  have hK (j : J) (v : Fin I.n) : (⟨j,v⟩ : Σ _ : J, Fin I.n) ∈ K ↔ v ∈ U ∧ h v = j := by
    simp [K, eq_comm]
  have hq : (∏ p ∈ K, (μ p (Z p)).toReal) = I.nuU U z := by
    unfold Inst.nuU
    rw [Finset.prod_image]
    intro x hx y hy he
    exact congrArg Sigma.snd he
  have hevent (x : (p : Σ _ : J, Fin I.n) → Fin (I.q p.2)) :
      (∀ p ∈ K, x p = Z p) ↔ ∀ v ∈ U, (E x) (h v) v = z v := by
    simp [K, E, Z, Sigma.curry]
  have hpin (x : (p : Σ _ : J, Fin I.n) → Fin (I.q p.2)) :
      E (fun p => if p ∈ K then Z p else x p) =
        (fun j v => if v ∈ U ∧ h v = j then z v else (E x) j v) := by
    funext j v
    simp [E, Z, hK, Sigma.curry]
  have hp := piLaw_pinning_expectation μ K Z (fun x => F (E x))
  rw [hq] at hp
  simp_rw [hweight] at hp
  have hleft : (∑ x, ((piLaw fun _ : J => I.prodLaw) (E x)).toReal *
      F (E (fun p => if p ∈ K then Z p else x p))) =
      ∑ ω : J → I.Assign, ((piLaw fun _ : J => I.prodLaw) ω).toReal *
        F (fun j v => if v ∈ U ∧ h v = j then z v else ω j v) := by
    calc
      _ = ∑ x, ((piLaw fun _ : J => I.prodLaw) (E x)).toReal *
          F (fun j v => if v ∈ U ∧ h v = j then z v else (E x) j v) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hpin x]
      _ = _ := by
        convert E.sum_comp (fun ω => ((piLaw fun _ : J => I.prodLaw) ω).toReal *
          F (fun j v => if v ∈ U ∧ h v = j then z v else ω j v)) using 1
  have hright : (∑ x, ((piLaw fun _ : J => I.prodLaw) (E x)).toReal *
      (if ∀ p ∈ K, x p = Z p then F (E x) else 0)) =
      ∑ ω : J → I.Assign, ((piLaw fun _ : J => I.prodLaw) ω).toReal *
        (if ∀ v ∈ U, ω (h v) v = z v then F ω else 0) := by
    calc
      _ = ∑ x, ((piLaw fun _ : J => I.prodLaw) (E x)).toReal *
          (if ∀ v ∈ U, (E x) (h v) v = z v then F (E x) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        have he := hevent x
        split_ifs <;> simp_all
      _ = _ := by
        convert E.sum_comp (fun ω => ((piLaw fun _ : J => I.prodLaw) ω).toReal *
          (if ∀ v ∈ U, ω (h v) v = z v then F ω else 0)) using 1
  convert hp using 1
  · congr 1
    convert hleft.symm using 1
    apply Finset.sum_congr
    · ext x; simp
    · intro x hx
      apply congrArg (fun u => ((piLaw fun _ : J => I.prodLaw) (E x)).toReal * F (E u))
      funext p
      by_cases hh : p ∈ K <;> simp [hh]
  · convert hright.symm using 1
    apply Finset.sum_congr
    · ext x; simp
    · intro x hx
      by_cases he : ∀ p ∈ K, x p = Z p <;> simp [he]


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


private theorem pin_mask_observational (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign) (ω : I.ExpSpace)
    (hT : T ∈ I.twoTrees D a) :
    let h : Fin I.n → Fin I.m ⊕ Finset (Fin I.m) := fun v =>
      if hv : ∃ t, t ∈ T ∧ v ∈ I.vbl t then Sum.inl hv.choose else Sum.inr T
    let ω' : I.ExpSpace := fun j v =>
      if v ∈ I.UT D T ∧ h v = j then z v else ω j v
    I.Llist D a (I.pin (T,z) ω) = I.Llist D a ω' := by
  dsimp only
  let h : Fin I.n → Fin I.m ⊕ Finset (Fin I.m) := fun v =>
    if hv : ∃ t, t ∈ T ∧ v ∈ I.vbl t then Sum.inl hv.choose else Sum.inr T
  let ω' : I.ExpSpace := fun j v =>
    if v ∈ I.UT D T ∧ h v = j then z v else ω j v
  change I.Llist D a (I.pin (T,z) ω) = I.Llist D a ω'
  have htree : I.IsTwoTree D a T := (Finset.mem_filter.mp hT).2
  have hinl (v : Fin I.n) (t : Fin I.m) (ht : t ∈ T) (hv : v ∈ I.vbl t) :
      v ∈ I.UT D T ∧ h v = Sum.inl t := by
    have hut : v ∈ I.UT D T := by
      unfold Inst.UT Inst.NDc
      exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_union_left _ ht, hv⟩
    refine ⟨hut, ?_⟩
    have hex : ∃ s, s ∈ T ∧ v ∈ I.vbl s := ⟨t, ht, hv⟩
    have hc := Classical.choose_spec hex
    have heq : Classical.choose hex = t := by
      by_contra hne
      have hadj : I.G.Adj (Classical.choose hex) t := by
        change Classical.choose hex ≠ t ∧ (I.vbl (Classical.choose hex) ∩ I.vbl t).Nonempty
        exact ⟨hne, ⟨v, Finset.mem_inter.mpr ⟨hc.2, hv⟩⟩⟩
      exact htree.2.2.1 _ hc.1 _ ht hadj
    simp [h, hex, heq]
  have hinl_mem (v : Fin I.n) (t : Fin I.m) (heq : h v = Sum.inl t) : t ∈ T := by
    by_cases hex : ∃ s, s ∈ T ∧ v ∈ I.vbl s
    · have hval : (Sum.inl (Classical.choose hex) : Fin I.m ⊕ Finset (Fin I.m)) = Sum.inl t := by simpa [h, hex] using heq
      have ht : Classical.choose hex = t := Sum.inl.inj hval
      simpa [ht] using (Classical.choose_spec hex).1
    · simp [h, hex] at heq
  have hinr_eq (v : Fin I.n) (S : Finset (Fin I.m)) (heq : h v = Sum.inr S) : S = T := by
    by_cases hex : ∃ s, s ∈ T ∧ v ∈ I.vbl s
    · simp [h, hex] at heq
    · simpa [h, hex] using heq.symm
  have hsig (S : Finset (Fin I.m)) :
      I.sigT D S (I.pin (T,z) ω) = I.sigT D S ω' := by
    apply funext
    intro v
    by_cases hv : v ∈ I.UT D S
    · by_cases hex : ∃ t, t ∈ S ∧ v ∈ I.vbl t
      · have hvbl := (Classical.choose_spec hex).2
        let t := Classical.choose hex
        have hvbl' : v ∈ I.vbl t := hvbl
        by_cases ht : t ∈ T
        · have hm := hinl v t ht hvbl'
          simp [Inst.sigT, Inst.restr, hv, hex, Inst.pin, ω', hm, t, ht]
        · have hm : ¬ (v ∈ I.UT D T ∧ h v = Sum.inl t) := by
            rintro ⟨_, heq⟩
            exact ht (hinl_mem v t heq)
          simp [Inst.sigT, Inst.restr, hv, hex, Inst.pin, ω', hm, t, ht]
      · by_cases hST : S = T
        · subst S
          have hm : v ∈ I.UT D T ∧ h v = Sum.inr T := ⟨hv, by simp [h, hex]⟩
          simp [Inst.sigT, Inst.restr, hv, hex, Inst.pin, ω', hm]
        · have hm : ¬ (v ∈ I.UT D T ∧ h v = Sum.inr S) := by
            rintro ⟨_, heq⟩
            exact hST (hinr_eq v S heq)
          simp [Inst.sigT, Inst.restr, hv, hex, Inst.pin, ω', hm, hST]
    · simp [Inst.sigT, Inst.restr, hv]
  simp only [Inst.Llist, hsig]



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

private theorem lemma_6_3_entry_probability (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if (T,z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) = I.nuU (I.UT D T) z := by
  simp_rw [valid_entry_mem_iff_sigT I D a T z _ hT hz]
  exact sigT_probability I D T z (Finset.mem_filter.mp hz).2


set_option maxHeartbeats 2000000 in

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if (T, z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) = I.nuU (I.UT D T) z ∧
    ∀ L : Finset (Finset (Fin I.m) × I.Assign),
      (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
        (if I.Llist D a ω = L ∧ (T, z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) =
      I.nuU (I.UT D T) z *
        (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
          (if I.Le D a (T, z) ω = L then (1 : ℝ) else 0)) := by
  refine ⟨lemma_6_3_entry_probability I D a T z hT hz, ?_⟩
  intro L
  let h : Fin I.n → Fin I.m ⊕ Finset (Fin I.m) := fun v =>
    if hv : ∃ t, t ∈ T ∧ v ∈ I.vbl t then Sum.inl hv.choose else Sum.inr T
  let F : I.ExpSpace → ℝ := fun ω => if I.Llist D a ω = L then 1 else 0
  have hevent (ω : I.ExpSpace) :
      ((T,z) ∈ I.Llist D a ω) ↔ ∀ v ∈ I.UT D T, ω (h v) v = z v := by
    rw [valid_entry_mem_iff_sigT I D a T z ω hT hz]
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
      · have hc := congrFun (Finset.mem_filter.mp hz).2 v
        simpa [Inst.sigT, Inst.restr, hv] using hc.symm
  have hmask (ω : I.ExpSpace) :
      I.Llist D a (I.pin (T,z) ω) =
        I.Llist D a (fun j v => if v ∈ I.UT D T ∧ h v = j then z v else ω j v) :=
    pin_mask_observational I D a T z ω hT
  have hp := assembled_pinning_expectation I (Fin I.m ⊕ Finset (Fin I.m)) (I.UT D T) z h F
  convert hp.symm using 1
  · apply Finset.sum_congr
    · ext ω; simp
    · intro ω hω
      have he := hevent ω
      by_cases hlist : I.Llist D a ω = L <;>
        by_cases hentry : (T,z) ∈ I.Llist D a ω <;>
        simp_all [F, Inst.expLaw]
  · congr 1
    apply Finset.sum_congr
    · ext ω; simp
    · intro ω hω
      simp only [F, Inst.expLaw, Inst.Le]
      apply congrArg (fun t : ℝ => ((piLaw fun _ : Fin I.m ⊕ Finset (Fin I.m) => I.prodLaw) ω).toReal * t)
      apply ite_congr
      · apply propext
        constructor
        · intro hl
          convert (hmask ω).symm.trans hl using 1
          congr 1
          funext j v
          by_cases hc : v ∈ I.UT D T ∧ h v = j <;> simp [hc]
        · intro hl
          apply (hmask ω).trans
          convert hl using 1
          congr 1
          funext j v
          by_cases hc : v ∈ I.UT D T ∧ h v = j <;> simp [hc]
      · intro _; rfl
      · intro _; rfl

