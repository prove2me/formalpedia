-- Prove2me | solution 1 for AutomorphicForm.twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b6615c40-c1a7-5dfd-a3fa-e6f292c5ff07

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one

set_option autoImplicit false

open scoped TensorProduct

section Generic

variable {G : Type*} [Group G]

private theorem mul_prod_range_iterate (f : G →* G) {t δ : G} (h : t * δ = δ * f t) (n : ℕ) :
    t * ((List.range n).map fun i => (⇑f)^[i] δ).prod =
      ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc, ih, mul_assoc, mul_assoc, Function.iterate_succ_apply]
    congr 1
    have h' := congrArg ((⇑f)^[n]) h
    rwa [iterate_map_mul, iterate_map_mul] at h'

end Generic

section Ring

open AutomorphicForm

variable {A : Type*} [CommRing A]

private theorem exists_eq_smul_one_add_smul_of_mul_eq_mul {G X : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X) :
    ∃ l m : A, X = l • (1 : Matrix (Fin 2) (Fin 2) A) + m • G := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨u, hu⟩ := hd
  have hu1 : (↑u⁻¹ : A) * ↑u = 1 := u.inv_mul
  have h00 : (X * G) 0 0 = (G * X) 0 0 := by rw [hX]
  have h01 : (X * G) 0 1 = (G * X) 0 1 := by rw [hX]
  have h10 : (X * G) 1 0 = (G * X) 1 0 := by rw [hX]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  obtain ⟨Z, hZ⟩ : ∃ Z : A,
      Z = (G 0 0 - G 1 1) * (X 0 0 - X 1 1) + 2 * (G 1 0 * X 0 1 + G 0 1 * X 1 0) := ⟨_, rfl⟩
  refine ⟨X 0 0 - (↑u⁻¹ : A) * Z * G 0 0, (↑u⁻¹ : A) * Z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
    linear_combination (-(X 0 1)) * hu1 + (X 0 1 * (↑u⁻¹ : A)) * hu -
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h00 -
      ((↑u⁻¹ : A) * G 0 1) * hZ
  · simp
    linear_combination (-(X 1 0)) * hu1 + (X 1 0 * (↑u⁻¹ : A)) * hu +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * h10 - (2 * (↑u⁻¹ : A) * G 1 0) * h00 -
      ((↑u⁻¹ : A) * G 1 0) * hZ
  · simp
    linear_combination (X 0 0 - X 1 1) * hu1 - ((X 0 0 - X 1 1) * (↑u⁻¹ : A)) * hu -
      (2 * (↑u⁻¹ : A) * G 1 0) * h01 + (2 * (↑u⁻¹ : A) * G 0 1) * h10 +
      ((↑u⁻¹ : A) * (G 0 0 - G 1 1)) * hZ

private theorem commute_of_mul_eq_mul_of_mul_eq_mul {G X Y : Matrix (Fin 2) (Fin 2) A}
    (hd : IsUnit (Matrix.trace G ^ 2 - 4 * Matrix.det G)) (hX : X * G = G * X)
    (hY : Y * G = G * Y) :
    Commute X Y := by
  obtain ⟨l, m, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hX
  obtain ⟨l', m', rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hd hY
  have c1 : Commute (1 : Matrix (Fin 2) (Fin 2) A) (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_left _).smul_right l').add_right ((Commute.one_left G).smul_right m')
  have c2 : Commute G (l' • (1 : Matrix (Fin 2) (Fin 2) A) + m' • G) :=
    ((Commute.one_right G).smul_right l').add_right ((Commute.refl G).smul_right m')
  exact (c1.smul_left l).add_left (c2.smul_left m)

private theorem commute_of_mem_centralizer_of_isRegularSemisimple {g : GL (Fin 2) A}
    (hg : IsRegularSemisimple g) {x y : GL (Fin 2) A}
    (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hy : y ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy
  have hx' : (x : Matrix (Fin 2) (Fin 2) A) * g = g * x := congrArg Units.val hx
  have hy' : (y : Matrix (Fin 2) (Fin 2) A) * g = g * y := congrArg Units.val hy
  exact Units.ext (commute_of_mul_eq_mul_of_mul_eq_mul hg hx' hy').eq

end Ring

section Twisted

open AutomorphicForm

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem twistedCentralizer_le_centralizer_normString_of_iterate (σ : L ≃ₐ[K] L)
    (hσ : ∀ t : GL (Fin 2) (L ⊗[K] A), (⇑(sigmaGL K L A σ))^[Module.finrank K L] t = t)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ht' : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
  have key := mul_prod_range_iterate (sigmaGL K L A σ) (mul_inv_eq_iff_eq_mul.mp ht')
    (Module.finrank K L)
  rw [hσ t] at key
  exact key

private theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (σ * σ') z = sigmaTensor K L A σ (sigmaTensor K L A σ' z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.one_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaGL_mul_apply (σ σ' : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A (σ * σ') g = sigmaGL K L A σ (sigmaGL K L A σ' g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A (σ * σ')) g i j =
    Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)
      (Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ') g) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_mul_apply]

private theorem sigmaGL_one_apply (g : GL (Fin 2) (L ⊗[K] A)) : sigmaGL K L A 1 g = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A 1) g i j = g i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_one_apply]

private theorem sigmaGL_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] g = sigmaGL K L A (σ ^ n) g := by
  induction n with
  | zero => simp [sigmaGL_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaGL_mul_apply]

private theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

private theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  rw [sigmaGL_iterate, pow_finrank_eq_one, sigmaGL_one_apply]

private theorem twistedCentralizer_le_centralizer_normString [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) :=
  twistedCentralizer_le_centralizer_normString_of_iterate K L A σ
    (sigmaGL_iterate_finrank K L A σ) δ

private theorem sigmaTensor_tmul (σ : L ≃ₐ[K] L) (x : L) (a : A) :
    sigmaTensor K L A σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
  simp [sigmaTensor]

private theorem sigmaGL_toTensorGL (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A γ) = toTensorGL K L A γ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ) (toTensorGL K L A γ) i j = toTensorGL K L A γ i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  show sigmaTensor K L A σ (Matrix.GeneralLinearGroup.map _ γ i j) = Matrix.GeneralLinearGroup.map _ γ i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, sigmaTensor_tmul,
    map_one]

private theorem coe_toTensorGL (γ : GL (Fin 2) A) :
    ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (γ : Matrix (Fin 2) (Fin 2) A).map
        (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom := by
  ext i j
  rw [Matrix.map_apply]
  exact Matrix.GeneralLinearGroup.map_apply _ i j γ

private theorem isRegularSemisimple_toTensorGL {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ) :
    IsRegularSemisimple (toTensorGL K L A γ) := by
  unfold IsRegularSemisimple at hγ ⊢
  rw [coe_toTensorGL]
  set ι : A →+* L ⊗[K] A := (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom with hι
  set M : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hM
  have htr : Matrix.trace (M.map ι) = ι (Matrix.trace M) := by simp [Matrix.trace]
  have hdet : Matrix.det (M.map ι) = ι (Matrix.det M) := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdisc : Matrix.trace (M.map ι) ^ 2 - 4 * Matrix.det (M.map ι) =
      ι (Matrix.trace M ^ 2 - 4 * Matrix.det M) := by
    rw [htr, hdet, map_sub, map_pow, map_mul, map_ofNat]
  rw [hdisc]
  exact hγ.map ι

private theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

private theorem toTensorGL_injective : Function.Injective (toTensorGL K L A) := by
  intro g h hgh
  have hgh' := congrArg (fun u : GL (Fin 2) (L ⊗[K] A) => (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hgh
  simp only [coe_toTensorGL] at hgh'
  refine Units.ext (Matrix.ext fun i j => includeRight_injective K L A ?_)
  have := congrFun (congrFun hgh' i) j
  simpa only [Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this

private theorem exists_algebraMap_eq_of_fixed (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    {x : L} (hx : σ x = x) : ∃ k : K, algebraMap K L k = x := by
  by_contra hcon
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      refine hcon ⟨-s / t, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one]
      apply smul_right_injective L ht
      show t • ((-s / t) • (1 : L)) = t • x
      have htt : t * (-s / t) = -s := by field_simp
      rw [smul_smul, htt, neg_smul, eq_neg_of_add_eq_zero_right hst]
  have hspan : Submodule.span K (Set.range ![(1 : L), x]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hdeg])
  apply hσ
  ext y
  have hfix : ∀ z ∈ Set.range ![(1 : L), x],
      (σ.toLinearMap : L →ₗ[K] L) z = (LinearMap.id : L →ₗ[K] L) z := by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · simp
    · simpa using hx
  have h := LinearMap.congr_fun (LinearMap.ext_on hspan hfix) y
  simpa using h

private theorem exists_includeRight_eq_of_sigmaTensor_eq (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hσ : σ ≠ 1) {z : L ⊗[K] A} (hz : sigmaTensor K L A σ z = z) :
    ∃ a : A, (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a = z := by
  set f : K →ₗ[K] L := Algebra.linearMap K L with hf
  set g : L →ₗ[K] L := σ.toLinearMap - LinearMap.id with hg
  have hexact : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext y
    simp only [LinearMap.mem_ker, hg, LinearMap.sub_apply, AlgEquiv.toLinearMap_apply, LinearMap.id_apply,
      sub_eq_zero, LinearMap.mem_range, hf, Algebra.linearMap_apply]
    constructor
    · intro hy
      exact exists_algebraMap_eq_of_fixed K L hdeg σ hσ hy
    · rintro ⟨k, rfl⟩
      exact σ.commutes k
  have hexactA := Module.Flat.rTensor_exact A hexact
  have hrT : ∀ w : L ⊗[K] A, LinearMap.rTensor A σ.toLinearMap w = sigmaTensor K L A σ w := by
    intro w
    refine TensorProduct.induction_on w ?_ ?_ ?_
    · simp
    · intro l a
      rw [LinearMap.rTensor_tmul, sigmaTensor_tmul, AlgEquiv.toLinearMap_apply]
    · intro u v hu hv
      rw [map_add, map_add, hu, hv]
  have hzker : LinearMap.rTensor A g z = 0 := by
    rw [hg, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_id, LinearMap.id_apply, hrT, hz,
      sub_self]
  obtain ⟨w, hw⟩ := (hexactA z).mp hzker
  obtain ⟨w', rfl⟩ : ∃ w' : A, (TensorProduct.lid K A).symm w' = w := ⟨TensorProduct.lid K A w, by simp⟩
  refine ⟨w', ?_⟩
  rw [← hw]
  simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, hf, Algebra.linearMap_apply, map_one,
    Algebra.TensorProduct.includeRight_apply]

private theorem sigmaGL_apply_coe (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sigmaTensor K L A σ ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j g

private theorem exists_map_eq_of_forall_sigmaTensor_eq (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hσ : σ ≠ 1) (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (hM : ∀ i j, sigmaTensor K L A σ (M i j) = M i j) :
    ∃ N : Matrix (Fin 2) (Fin 2) A,
      N.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom = M := by
  choose N hN using fun i j => exists_includeRight_eq_of_sigmaTensor_eq K L A hdeg σ hσ (hM i j)
  refine ⟨Matrix.of N, ?_⟩
  ext i j
  simpa only [Matrix.map_apply, Matrix.of_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hN i j

private theorem exists_toTensorGL_eq_of_sigmaGL_eq (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    {g : GL (Fin 2) (L ⊗[K] A)} (hg : sigmaGL K L A σ g = g) : ∃ h : GL (Fin 2) A, toTensorGL K L A h = g := by
  set ι : A →+* L ⊗[K] A := (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom with hι
  have hginv : sigmaGL K L A σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  have hfix : ∀ u : GL (Fin 2) (L ⊗[K] A), sigmaGL K L A σ u = u →
      ∀ i j, sigmaTensor K L A σ ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) =
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j := by
    intro u hu i j
    rw [← sigmaGL_apply_coe, hu]
  obtain ⟨N₀, hN₀⟩ := exists_map_eq_of_forall_sigmaTensor_eq K L A hdeg σ hσ _ (hfix g hg)
  obtain ⟨N₁, hN₁⟩ := exists_map_eq_of_forall_sigmaTensor_eq K L A hdeg σ hσ _ (hfix g⁻¹ hginv)
  have hinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) A => M.map ι :=
    Matrix.map_injective (includeRight_injective K L A)
  have h₀₁ : N₀ * N₁ = 1 := by
    apply hinj
    simp only [Matrix.map_mul, Matrix.map_one ι (map_zero ι) (map_one ι)]
    rw [hN₀, hN₁]
    exact g.val_inv
  have h₁₀ : N₁ * N₀ = 1 := by
    apply hinj
    simp only [Matrix.map_mul, Matrix.map_one ι (map_zero ι) (map_one ι)]
    rw [hN₀, hN₁]
    exact g.inv_val
  refine ⟨⟨N₀, N₁, h₀₁, h₁₀⟩, ?_⟩
  apply Units.ext
  rw [coe_toTensorGL]
  exact hN₀

end Twisted

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormConjugator K L A σ γ δ 1) :
    AutomorphicForm.twistedCentralizer K L A σ δ =
      (Subgroup.centralizer {γ}).map (AutomorphicForm.toTensorGL K L A) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdeg]; exact two_pos)
  have hNδ : normString K L A σ δ = toTensorGL K L A γ := by
    have h : toTensorGL K L A γ = (1 : GL (Fin 2) (L ⊗[K] A))⁻¹ * normString K L A σ δ * 1 := hN
    rwa [inv_one, one_mul, mul_one, eq_comm] at h
  have hreg : IsRegularSemisimple (toTensorGL K L A γ) := isRegularSemisimple_toTensorGL K L A hγ
  have hσγ : sigmaGL K L A σ (toTensorGL K L A γ) = toTensorGL K L A γ := sigmaGL_toTensorGL K L A σ γ
  have hN2 : normString K L A σ δ = δ * sigmaGL K L A σ δ := by
    unfold normString
    rw [hdeg]
    simp [List.range_succ]
  have hσ2 : sigmaGL K L A σ (sigmaGL K L A σ δ) = δ := by
    have h := sigmaGL_iterate_finrank K L A σ δ
    rw [hdeg] at h
    simpa only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] using h
  have hswap : sigmaGL K L A σ δ * δ = δ * sigmaGL K L A σ δ := by
    have h : sigmaGL K L A σ (normString K L A σ δ) = normString K L A σ δ := by rw [hNδ, hσγ]
    rwa [hN2, map_mul, hσ2] at h
  have hδmem : δ ∈ Subgroup.centralizer ({toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hNδ, hN2, mul_assoc, hswap]
  ext t
  constructor
  · intro ht
    have htN := twistedCentralizer_le_centralizer_normString K L A σ δ ht
    rw [hNδ] at htN
    have htδ : Commute t δ := commute_of_mem_centralizer_of_isRegularSemisimple hreg htN hδmem
    have ht' : t * δ * (sigmaGL K L A σ t)⁻¹ = δ := ht
    have hfix : sigmaGL K L A σ t = t := by
      rw [htδ.eq, mul_inv_eq_iff_eq_mul] at ht'
      exact (mul_left_cancel ht').symm
    obtain ⟨s, rfl⟩ := exists_toTensorGL_eq_of_sigmaGL_eq K L A hdeg σ hσ hfix
    refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at htN ⊢
    apply toTensorGL_injective K L A
    rw [map_mul, map_mul]
    exact htN
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    show toTensorGL K L A s * δ * (sigmaGL K L A σ (toTensorGL K L A s))⁻¹ = δ
    rw [sigmaGL_toTensorGL]
    have hsmem : toTensorGL K L A s ∈
        Subgroup.centralizer ({toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hs ⊢
      rw [← map_mul, ← map_mul, hs]
    have hc : Commute (toTensorGL K L A s) δ :=
      commute_of_mem_centralizer_of_isRegularSemisimple hreg hsmem hδmem
    rw [hc.eq, mul_inv_cancel_right]

end S_AutomorphicForm_twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one
end P2MW
export P2MW.S_AutomorphicForm_twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one (solution)
