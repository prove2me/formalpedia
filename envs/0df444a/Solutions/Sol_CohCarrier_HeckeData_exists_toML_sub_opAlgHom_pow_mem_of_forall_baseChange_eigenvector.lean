-- Prove2me | solution 1 for CohCarrier.HeckeData.exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/43d013a4-2acb-539e-9c6d-5e17106373c1

import Mathlib
import Definitions.Def_CohCarrier_HeckeData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_HeckeData_exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier
open scoped TensorProduct

namespace ResidNilpotence

section CommonEigenvector

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {ι : Type*} (f : ι → Module.End K W) (χ : ι → K)

def eigInf (F : Finset ι) : Submodule K W := ⨅ i ∈ F, (f i).eigenspace (χ i)

theorem eigInf_mono {F G : Finset ι} (h : F ⊆ G) : eigInf f χ G ≤ eigInf f χ F :=
  biInf_mono h

theorem mem_eigInf_iff (F : Finset ι) (w : W) :
    w ∈ eigInf f χ F ↔ ∀ i ∈ F, f i w = χ i • w := by
  simp [eigInf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem eigInf_ne_bot [Nontrivial W] (hcomm : ∀ i j, Commute (f i) (f j))
    (hnil : ∀ i, IsNilpotent (f i - algebraMap K (Module.End K W) (χ i))) (F : Finset ι) :
    eigInf f χ F ≠ ⊥ := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [eigInf, Finset.notMem_empty, not_false_eq_true, iInf_neg, iInf_top, ne_eq, top_ne_bot]
  | insert i F hi ih =>

    set U := eigInf f χ F with hU
    set Nf : Module.End K W := f i - algebraMap K (Module.End K W) (χ i) with hNf
    have hmaps : ∀ u ∈ U, Nf u ∈ U := by
      intro u hu
      rw [hU, mem_eigInf_iff] at hu ⊢
      intro j hj
      simp only [hNf, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, map_smul]
      rw [hu j hj]
      have hc := hcomm j i
      rw [show f j (f i u) = f i (f j u) from LinearMap.congr_fun hc.eq u, hu j hj, map_smul,
        smul_sub, smul_comm (χ i) (χ j) u]
    obtain ⟨m, hm⟩ := hnil i

    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
    have hex : ∃ t : ℕ, (Nf ^ t) u ≠ 0 ∧ (Nf ^ (t + 1)) u = 0 := by
      have hzero : (Nf ^ m) u = 0 := by rw [hm]; rfl

      have hP : ∃ t : ℕ, (Nf ^ t) u = 0 := ⟨m, hzero⟩
      let t₀ := Nat.find hP
      have ht₀ : (Nf ^ t₀) u = 0 := Nat.find_spec hP
      have ht₀pos : 0 < t₀ := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        apply hu0
        have := ht₀
        rw [show t₀ = 0 from h0, pow_zero] at this
        exact this
      refine ⟨t₀ - 1, ?_, ?_⟩
      · exact Nat.find_min hP (Nat.sub_one_lt_of_lt ht₀pos)
      · rw [Nat.sub_add_cancel ht₀pos]; exact ht₀
    obtain ⟨t, ht1, ht2⟩ := hex
    have hwU : (Nf ^ t) u ∈ U := by
      induction t with
      | zero => simpa using huU
      | succ t iht =>
        rw [pow_succ', Module.End.mul_apply]
        exact hmaps _ (by

          clear iht ht1 ht2
          induction t with
          | zero => simpa using huU
          | succ t ih2 => rw [pow_succ', Module.End.mul_apply]; exact hmaps _ ih2)
    intro hbot
    apply ht1
    have hmem : (Nf ^ t) u ∈ eigInf f χ (insert i F) := by
      rw [mem_eigInf_iff]
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      ·
        have : Nf ((Nf ^ t) u) = 0 := by
          rw [← Module.End.mul_apply, ← pow_succ', ht2]
        simp only [hNf, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at this
        exact this
      · exact (mem_eigInf_iff f χ F _).mp hwU j hj
    rw [hbot] at hmem
    exact (Submodule.mem_bot K).mp hmem

theorem exists_common_eigenvector [Nontrivial W] (hcomm : ∀ i j, Commute (f i) (f j))
    (hnil : ∀ i, IsNilpotent (f i - algebraMap K (Module.End K W) (χ i))) :
    ∃ w : W, w ≠ 0 ∧ ∀ i, f i w = χ i • w := by
  classical

  have hne : ∃ d : ℕ, ∃ F : Finset ι, Module.finrank K (eigInf f χ F) = d := ⟨_, ∅, rfl⟩
  obtain ⟨F₀, hF₀⟩ := Nat.find_spec hne
  have hmin : ∀ F : Finset ι, Module.finrank K (eigInf f χ F₀) ≤ Module.finrank K (eigInf f χ F) := by
    intro F
    rw [hF₀]
    exact Nat.find_min' hne ⟨F, rfl⟩

  have hall : ∀ i, eigInf f χ F₀ ≤ (f i).eigenspace (χ i) := by
    intro i
    have hle : eigInf f χ (insert i F₀) ≤ eigInf f χ F₀ := eigInf_mono f χ (Finset.subset_insert i F₀)
    have heq : eigInf f χ (insert i F₀) = eigInf f χ F₀ :=
      Submodule.eq_of_le_of_finrank_le hle (hmin _)
    intro w hw
    rw [← heq, mem_eigInf_iff] at hw
    exact (Module.End.mem_eigenspace_iff).mpr (hw i (Finset.mem_insert_self i F₀))
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (eigInf_ne_bot f χ hcomm hnil F₀)
  exact ⟨w, hw0, fun i => (Module.End.mem_eigenspace_iff).mp (hall i hw)⟩

end CommonEigenvector

end ResidNilpotence

namespace ResidNilpotence

section Kill

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

theorem commute_aeval_self (f : Module.End K W) (Q : Polynomial K) :
    Commute (Polynomial.aeval f Q) f := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_left c f).mul_left ((Commute.refl f).pow_left n)

theorem aeval_apply_eq_zero_of_mem_maxGenEigenspace (f : Module.End K W) {P Q : Polynomial K}
    {a b : K} (hab : a ≠ b) (m : ℕ) (hP : P = (Polynomial.X - Polynomial.C a) ^ m * Q)
    (hPf : Polynomial.aeval f P = 0) {w : W} (hw : w ∈ f.maxGenEigenspace b) :
    Polynomial.aeval f Q w = 0 := by
  set U := f.maxGenEigenspace b with hU
  set g : Module.End K W := f - algebraMap K (Module.End K W) a with hg

  have hinj : ∀ y ∈ U, g y = 0 → y = 0 := by
    intro y hyU hy
    have hya : y ∈ f.maxGenEigenspace a := by
      rw [Module.End.mem_maxGenEigenspace]
      exact ⟨1, by simpa [hg] using hy⟩
    have hd := Module.End.disjoint_genEigenspace f hab ⊤ ⊤
    exact (Submodule.disjoint_def.mp hd) y hya hyU
  have hgU : ∀ y ∈ U, g y ∈ U := fun y hy =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f a) b hy
  have hinjm : ∀ (n : ℕ) (y : W), y ∈ U → (g ^ n) y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y _ hy; simpa using hy
    | succ n ih =>
      intro y hyU hy
      rw [pow_succ, Module.End.mul_apply] at hy
      exact hinj y hyU (ih (g y) (hgU y hyU) hy)

  have hQU : Polynomial.aeval f Q w ∈ U :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (commute_aeval_self f Q).symm b hw
  refine hinjm m _ hQU ?_
  have hfac : g ^ m * Polynomial.aeval f Q = Polynomial.aeval f P := by
    rw [hP, map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [← Module.End.mul_apply, hfac, hPf, LinearMap.zero_apply]

end Kill

end ResidNilpotence

namespace ResidNilpotence

section TensorZero

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] {k : Type*} [Field k] [Algebra 𝒪 k]
variable {V : Type*} [AddCommGroup V] [Module 𝒪 V]

theorem ker_algebraMap_eq_maximalIdeal (hk : Function.Surjective (algebraMap 𝒪 k)) :
    RingHom.ker (algebraMap 𝒪 k) = IsLocalRing.maximalIdeal 𝒪 :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)

theorem mem_smul_top_of_one_tmul_eq_zero_aux (I : Ideal 𝒪) (q : (𝒪 ⧸ I) ≃ₐ[𝒪] k)
    (w : V) (hw : (1 : k) ⊗ₜ[𝒪] w = 0) : w ∈ I • (⊤ : Submodule 𝒪 V) := by
  have h0 : (1 : 𝒪 ⧸ I) ⊗ₜ[𝒪] w = 0 := by
    have : (TensorProduct.congr q.symm.toLinearEquiv (LinearEquiv.refl 𝒪 V)) ((1 : k) ⊗ₜ[𝒪] w)
        = (1 : 𝒪 ⧸ I) ⊗ₜ[𝒪] w := by
      rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, map_one]
    rw [← this, hw, map_zero]
  have h2 := TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := V) I 1 w
  rw [map_one, one_smul, h0, map_zero] at h2
  exact (Submodule.Quotient.mk_eq_zero _).mp h2.symm

theorem mem_maximalIdeal_smul_of_one_tmul_eq_zero (hk : Function.Surjective (algebraMap 𝒪 k))
    (w : V) (hw : (1 : k) ⊗ₜ[𝒪] w = 0) :
    w ∈ (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 V) := by
  have hk' : Function.Surjective (Algebra.ofId 𝒪 k) := hk
  have hI : RingHom.ker (Algebra.ofId 𝒪 k) = IsLocalRing.maximalIdeal 𝒪 := by
    rw [← ker_algebraMap_eq_maximalIdeal hk]
    ext a
    simp only [RingHom.mem_ker]
    rfl
  rw [← hI]
  exact mem_smul_top_of_one_tmul_eq_zero_aux (RingHom.ker (Algebra.ofId 𝒪 k))
    (Ideal.quotientKerAlgEquivOfSurjective hk') w hw

theorem one_tmul_injective_field (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    {M : Type*} [AddCommGroup M] [Module k M] (y : M)
    (hy : (1 : K) ⊗ₜ[k] y = 0) : y = 0 := by

  have hinj : LinearMap.ker (Algebra.linearMap k K) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap k K).injective
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K) hinj
  have hπ1 : π 1 = 1 := by
    have := LinearMap.congr_fun hπ (1 : k)
    simpa using this
  have : (TensorProduct.lid k M) ((π.rTensor M) ((1 : K) ⊗ₜ[k] y)) = y := by
    rw [LinearMap.rTensor_tmul, hπ1, TensorProduct.lid_tmul, one_smul]
  rw [← this, hy, map_zero, map_zero]

variable (K : Type*) [Field K] [Algebra 𝒪 K] [Algebra k K] [IsScalarTower 𝒪 k K]

theorem mem_maximalIdeal_smul_of_one_tmul_eq_zero' (hk : Function.Surjective (algebraMap 𝒪 k))
    (w : V) (hw : (1 : K) ⊗ₜ[𝒪] w = 0) :
    w ∈ (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 V) := by
  apply mem_maximalIdeal_smul_of_one_tmul_eq_zero hk
  apply one_tmul_injective_field k K

  have h := TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul 𝒪 k K (1 : K) w

  rw [← h, hw, map_zero]

end TensorZero

section Localised

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {k : Type} [Field k] [Algebra 𝒪 k]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] (D : HeckeData 𝒪 V k)

theorem smul_mem_maximalIdeal_smul_ML (L : Localization D.mTheta.primeCompl) {y : D.ML}
    (hy : y ∈ (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML)) :
    L • y ∈ (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML) := by
  refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun y z hy hz => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [smul_add]; exact Submodule.add_mem _ hy hz

theorem toML_mem_of_smul_mem (m : V) (s : D.FreeAlg) (hs : s ∈ D.mTheta.primeCompl)
    (h : s • m ∈ (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 V)) :
    D.toML m ∈ (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML) := by
  have hsm : D.toML (s • m) ∈ (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML) := by
    have : D.toMLₒ (s • m) ∈ ((IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 V)).map D.toMLₒ :=
      Submodule.mem_map_of_mem h
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hcancel : D.toML m =
      (Localization.mk 1 ⟨s, hs⟩ : Localization D.mTheta.primeCompl) • D.toML (s • m) := by
    show LocalizedModule.mk m 1 =
      (Localization.mk 1 ⟨s, hs⟩ : Localization D.mTheta.primeCompl) • LocalizedModule.mk (s • m) 1
    rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    exact (LocalizedModule.mk_cancel ⟨s, hs⟩ m).symm
  rw [hcancel]
  exact smul_mem_maximalIdeal_smul_ML D _ hsm

end Localised

end ResidNilpotence

namespace ResidNilpotence

variable {𝒪 : Type} [CommRing 𝒪] {k : Type} [Field k] [Algebra 𝒪 k]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] (D : HeckeData 𝒪 V k)

theorem commute_opAlgHom (Z : Module.End 𝒪 V) (hZ : ∀ g : D.Gen, Z * D.op g = D.op g * Z)
    (s : D.FreeAlg) : Commute Z (D.opAlgHom s) := by
  induction s using MvPolynomial.induction_on with
  | C a =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (Algebra.commutes a Z).symm
  | add p q hp hq =>
      rw [map_add]
      exact hp.add_right hq
  | mul_X p g hp =>
      rw [map_mul, D.opAlgHom_X]
      exact hp.mul_right (hZ g)

theorem baseChange_opAlgHom_aeval_X (K : Type) [CommRing K] [Algebra 𝒪 K] (g : D.Gen)
    (Q : Polynomial 𝒪) :
    (D.opAlgHom (Polynomial.aeval (MvPolynomial.X g : D.FreeAlg) Q)).baseChange K =
      Polynomial.aeval ((D.op g).baseChange K) (Q.map (algebraMap 𝒪 K)) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, LinearMap.baseChange_add, hp, hq, Polynomial.map_add, map_add]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, map_mul, map_pow, AlgHom.commutes, D.opAlgHom_X,
        Polynomial.map_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
        LinearMap.baseChange_smul, LinearMap.baseChange_pow, algebraMap_smul]

theorem opAlgHom_baseChange_apply_of_forall_op (K : Type) [Field K] [Algebra 𝒪 K] [Algebra k K]
    [IsScalarTower 𝒪 k K] (x : K ⊗[𝒪] V)
    (hx : ∀ g : D.Gen, (D.op g).baseChange K x = algebraMap k K (D.θbar g) • x) (z : D.FreeAlg) :
    (D.opAlgHom z).baseChange K x = algebraMap k K (D.thetaTilde z) • x := by
  induction z using MvPolynomial.induction_on with
  | C a =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply, algebraMap_smul, Algebra.algebraMap_eq_smul_one,
        LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.smul_apply,
        Module.End.one_apply]
  | add p q hp hq =>
      rw [map_add, LinearMap.baseChange_add, LinearMap.add_apply, hp, hq, map_add, map_add, add_smul]
  | mul_X p g hp =>
      rw [map_mul, D.opAlgHom_X, LinearMap.baseChange_mul, Module.End.mul_apply, hx g,
        LinearMap.map_smul, hp, map_mul, map_mul, smul_smul, mul_comm]
      congr 2
      exact congrArg (algebraMap k K) (MvPolynomial.aeval_X (R := 𝒪) D.θbar g).symm

end ResidNilpotence

namespace ResidNilpotence

section Restrict

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {ι : Type*}

theorem restrict_sub_algebraMap_pow_apply (f : Module.End K W) (p : Submodule K W)
    (hp : ∀ x ∈ p, f x ∈ p) (c : K) (m : ℕ) (x : p) :
    (((f.restrict hp - algebraMap K (Module.End K p) c) ^ m) x : W) =
      ((f - algebraMap K (Module.End K W) c) ^ m) (x : W) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    simp [LinearMap.restrict_apply, Algebra.algebraMap_eq_smul_one]

theorem exists_common_eigenvector_of_submodule (f : ι → Module.End K W) (χ : ι → K)
    (p : Submodule K W) (hp : p ≠ ⊥) (hinv : ∀ i, ∀ x ∈ p, f i x ∈ p)
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hnil : ∀ i, ∃ m : ℕ, ∀ x ∈ p, ((f i - algebraMap K (Module.End K W) (χ i)) ^ m) x = 0) :
    ∃ w ∈ p, w ≠ 0 ∧ ∀ i, f i w = χ i • w := by
  haveI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
  let f' : ι → Module.End K p := fun i => (f i).restrict (hinv i)
  have hcomm' : ∀ i j, Commute (f' i) (f' j) := by
    intro i j
    ext x
    simp only [f', Module.End.mul_apply, LinearMap.restrict_apply]
    exact LinearMap.congr_fun (hcomm i j).eq x
  have hnil' : ∀ i, IsNilpotent (f' i - algebraMap K (Module.End K p) (χ i)) := by
    intro i
    obtain ⟨m, hm⟩ := hnil i
    refine ⟨m, ?_⟩
    ext x
    rw [restrict_sub_algebraMap_pow_apply]
    simpa using hm x x.2
  obtain ⟨w, hw0, hw⟩ := exists_common_eigenvector f' χ hcomm' hnil'
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h), fun i => ?_⟩
  have := congrArg Subtype.val (hw i)
  simpa [f', LinearMap.restrict_apply] using this

end Restrict

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {k : Type} [Field k] [Algebra 𝒪 k]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

theorem main (hk : Function.Surjective (algebraMap 𝒪 k)) (D : HeckeData 𝒪 V k)
    (Z : Module.End 𝒪 V) (hZ : ∀ g : D.Gen, Z * D.op g = D.op g * Z) (z₀ : D.FreeAlg)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra 𝒪 K] [Algebra k K] [IsScalarTower 𝒪 k K]
    (htest : ∀ (x : K ⊗[𝒪] V) (b : K), x ≠ 0 →
      (∀ g : D.Gen, (D.op g).baseChange K x = algebraMap k K (D.θbar g) • x) →
      Z.baseChange K x = b • x → b = algebraMap k K (D.thetaTilde z₀)) :
    ∃ n : ℕ, ∀ v : V,
      D.toML (((Z - D.opAlgHom z₀) ^ n) v) ∈
        (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML) := by
  classical

  set Xh : D.Gen → Module.End K (K ⊗[𝒪] V) := fun g => (D.op g).baseChange K with hXh
  set T : Module.End 𝒪 V := Z - D.opAlgHom z₀ with hT
  set Th : Module.End K (K ⊗[𝒪] V) := T.baseChange K with hTh
  set χ₀ : D.Gen → K := fun g => algebraMap k K (D.θbar g) with hχ₀
  set E : Submodule K (K ⊗[𝒪] V) := ⨅ g, (Xh g).maxGenEigenspace (χ₀ g) with hE
  set n : ℕ := Module.finrank K (K ⊗[𝒪] V) with hn

  have hopcomm : ∀ g : D.Gen, Commute (D.opAlgHom z₀) (D.op g) := by
    intro g
    rw [← D.opAlgHom_X g, commute_iff_eq, ← map_mul, ← map_mul, mul_comm]
  have hTcomm : ∀ g : D.Gen, Commute T (D.op g) := by
    intro g
    exact Commute.sub_left (hZ g) (hopcomm g)
  have hXX : ∀ g h : D.Gen, Commute (Xh g) (Xh h) := by
    intro g h
    show (D.op g).baseChange K * (D.op h).baseChange K = (D.op h).baseChange K * (D.op g).baseChange K
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, D.comm g h]
  have hTX : ∀ g : D.Gen, Commute Th (Xh g) := by
    intro g
    show T.baseChange K * (D.op g).baseChange K = (D.op g).baseChange K * T.baseChange K
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (hTcomm g).eq]

  have hTs : ∀ s : D.FreeAlg, Commute T (D.opAlgHom s) := by
    intro s
    refine Commute.sub_left (commute_opAlgHom D Z hZ s) ?_
    rw [commute_iff_eq, ← map_mul, ← map_mul, mul_comm]

  have hEX : ∀ g, ∀ x ∈ E, Xh g x ∈ E := by
    intro g x hx
    rw [hE, Submodule.mem_iInf] at hx ⊢
    intro h
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hXX h g) (χ₀ h) (hx h)
  have hET : ∀ x ∈ E, Th x ∈ E := by
    intro x hx
    rw [hE, Submodule.mem_iInf] at hx ⊢
    intro h
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hTX h).symm (χ₀ h) (hx h)

  have hμ : ∀ μ : K, μ ≠ 0 → E ⊓ Th.maxGenEigenspace μ = ⊥ := by
    intro μ hμ0
    by_contra hne

    set F := E ⊓ Th.maxGenEigenspace μ with hF
    have hFinv : ∀ o : Option D.Gen, ∀ x ∈ F,
        (Option.elim o Th Xh) x ∈ F := by
      rintro (_ | g) x ⟨hxE, hxT⟩
      · exact ⟨hET x hxE, Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl Th) μ hxT⟩
      · exact ⟨hEX g x hxE, Module.End.mapsTo_maxGenEigenspace_of_comm (hTX g) μ hxT⟩
    have hFcomm : ∀ o o' : Option D.Gen, Commute (Option.elim o Th Xh) (Option.elim o' Th Xh) := by
      rintro (_ | g) (_ | g')
      · exact Commute.refl _
      · exact hTX g'
      · exact (hTX g).symm
      · exact hXX g g'
    have hFnil : ∀ o : Option D.Gen, ∃ m : ℕ, ∀ x ∈ F,
        ((Option.elim o Th Xh - algebraMap K _ (Option.elim o μ χ₀)) ^ m) x = 0 := by
      rintro (_ | g)
      · refine ⟨n, fun x hx => ?_⟩
        have hx' : x ∈ Th.maxGenEigenspace μ := hx.2
        rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
          LinearMap.mem_ker] at hx'
        simpa [Algebra.algebraMap_eq_smul_one] using hx'
      · refine ⟨n, fun x hx => ?_⟩
        have hx' : x ∈ (Xh g).maxGenEigenspace (χ₀ g) := by
          have hxE : x ∈ E := hx.1
          rw [hE, Submodule.mem_iInf] at hxE
          exact hxE g
        rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
          LinearMap.mem_ker] at hx'
        simpa [Algebra.algebraMap_eq_smul_one] using hx'
    obtain ⟨w, hwF, hw0, hw⟩ := exists_common_eigenvector_of_submodule
      (fun o : Option D.Gen => Option.elim o Th Xh) (fun o => Option.elim o μ χ₀) F hne hFinv hFcomm hFnil

    have hwX : ∀ g : D.Gen, (D.op g).baseChange K w = algebraMap k K (D.θbar g) • w :=
      fun g => hw (some g)
    have hwT : Th w = μ • w := hw none
    have hwZ : Z.baseChange K w = (μ + algebraMap k K (D.thetaTilde z₀)) • w := by
      have h1 : Z.baseChange K w = Th w + (D.opAlgHom z₀).baseChange K w := by
        rw [hTh, hT, LinearMap.baseChange_sub, LinearMap.sub_apply, sub_add_cancel]
      rw [h1, hwT, opAlgHom_baseChange_apply_of_forall_op D K w hwX z₀, add_smul]
    have := htest w _ hw0 hwX hwZ
    exact hμ0 (by simpa using this)
  have hEle : E ≤ Th.maxGenEigenspace 0 := by
    have hdec : E = ⨆ μ : K, E ⊓ Th.genEigenspace μ ⊤ :=
      Submodule.eq_iSup_inf_genEigenspace ⊤ hET (Module.End.iSup_maxGenEigenspace_eq_top Th)
    intro x hx
    rw [hdec] at hx
    refine Submodule.iSup_induction (fun μ : K => E ⊓ Th.genEigenspace μ ⊤)
      (motive := fun x => x ∈ Th.maxGenEigenspace 0) hx ?_ (Submodule.zero_mem _)
      (fun x y hx hy => Submodule.add_mem _ hx hy)
    intro μ y hy
    by_cases hμ0 : μ = 0
    · subst hμ0; exact hy.2
    · have hbot : E ⊓ Th.genEigenspace μ ⊤ = ⊥ := hμ μ hμ0
      have hy' : y ∈ E ⊓ Th.genEigenspace μ ⊤ := hy
      rw [hbot] at hy'
      rw [(Submodule.mem_bot K).mp hy']
      exact Submodule.zero_mem _
  have hB : ∀ e ∈ E, (Th ^ n) e = 0 := by
    intro e he
    have := hEle he
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at this
    rw [← hn] at this
    have h0 : Th - (0 : K) • (1 : Module.End K (K ⊗[𝒪] V)) = Th := by ext v; simp
    convert this using 3
    exact h0.symm

  have hkill : ∀ χ : D.Gen → K, χ ≠ χ₀ → ∃ s : D.FreeAlg, s ∈ D.mTheta.primeCompl ∧
      ∀ x ∈ (⨅ g, (Xh g).maxGenEigenspace (χ g)), (D.opAlgHom s).baseChange K x = 0 := by
    intro χ hχ
    obtain ⟨g, hg⟩ := Function.ne_iff.mp hχ

    obtain ⟨P, hPmonic, hP⟩ := LinearMap.exists_monic_and_aeval_eq_zero 𝒪 (D.op g)

    set Pbar : Polynomial k := P.map (algebraMap 𝒪 k) with hPbar
    have hPbar0 : Pbar ≠ 0 := (hPmonic.map (algebraMap 𝒪 k)).ne_zero
    obtain ⟨Qbar, hfac, hndvd⟩ := Pbar.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hPbar0 (D.θbar g)
    have hQbar : Qbar.eval (D.θbar g) ≠ 0 := by
      intro h; exact hndvd (Polynomial.dvd_iff_isRoot.mpr h)
    obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (algebraMap 𝒪 k) hk Qbar
    refine ⟨Polynomial.aeval (MvPolynomial.X g : D.FreeAlg) Q, ?_, ?_⟩
    ·
      show Polynomial.aeval (MvPolynomial.X g : D.FreeAlg) Q ∉ D.mTheta
      intro hmem
      apply hQbar
      have h1 : D.thetaTilde (Polynomial.aeval (MvPolynomial.X g : D.FreeAlg) Q) = 0 := hmem
      have h2 : D.thetaTilde (MvPolynomial.X g) = D.θbar g := by
        simp [HeckeData.thetaTilde]
      rw [← Polynomial.aeval_algHom_apply, h2, Polynomial.aeval_def] at h1
      rw [← hQ, Polynomial.eval_map]
      exact h1
    · intro x hx
      rw [baseChange_opAlgHom_aeval_X]

      set m := Pbar.rootMultiplicity (D.θbar g)
      have hPK : P.map (algebraMap 𝒪 K) =
          (Polynomial.X - Polynomial.C (χ₀ g)) ^ m * Q.map (algebraMap 𝒪 K) := by
        have : P.map (algebraMap 𝒪 K) = Pbar.map (algebraMap k K) := by
          rw [hPbar, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
        rw [this, hfac, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, ← hQ, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      have hPK0 : Polynomial.aeval ((D.op g).baseChange K) (P.map (algebraMap 𝒪 K)) = 0 := by
        rw [← baseChange_opAlgHom_aeval_X D K g P, ← Polynomial.aeval_algHom_apply, D.opAlgHom_X, hP,
          LinearMap.baseChange_zero]
      have hxg : x ∈ (Xh g).maxGenEigenspace (χ g) := by
        rw [Submodule.mem_iInf] at hx; exact hx g
      exact aeval_apply_eq_zero_of_mem_maxGenEigenspace (Xh g) (Ne.symm hg) m hPK hPK0 hxg

  refine ⟨n, fun v => ?_⟩

  have htop : ⨆ χ : D.Gen → K, ⨅ g, (Xh g).maxGenEigenspace (χ g) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute Xh
      (fun g h _ => hXX g h) (fun g => Module.End.iSup_maxGenEigenspace_eq_top (Xh g))

  have hall : ∀ u : K ⊗[𝒪] V, ∃ s : D.FreeAlg, s ∈ D.mTheta.primeCompl ∧
      (Th ^ n) ((D.opAlgHom s).baseChange K u) = 0 := by
    intro u
    have hu : u ∈ ⨆ χ : D.Gen → K, ⨅ g, (Xh g).maxGenEigenspace (χ g) := by rw [htop]; trivial
    refine Submodule.iSup_induction (fun χ : D.Gen → K => ⨅ g, (Xh g).maxGenEigenspace (χ g))
      (motive := fun u => ∃ s : D.FreeAlg, s ∈ D.mTheta.primeCompl ∧
        (Th ^ n) ((D.opAlgHom s).baseChange K u) = 0) hu
      ?_ ⟨1, Submonoid.one_mem _, by simp⟩ ?_
    · intro χ x hx
      by_cases hχ : χ = χ₀
      · subst hχ
        refine ⟨1, Submonoid.one_mem _, ?_⟩
        rw [map_one, LinearMap.baseChange_one, Module.End.one_apply]
        exact hB x hx
      · obtain ⟨s, hs, hsx⟩ := hkill χ hχ
        exact ⟨s, hs, by rw [hsx x hx, map_zero]⟩
    · rintro x y ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
      refine ⟨s₁ * s₂, Submonoid.mul_mem _ hs₁ hs₂, ?_⟩
      have hc : ∀ s : D.FreeAlg, Commute (Th ^ n) ((D.opAlgHom s).baseChange K) := by
        intro s
        apply Commute.pow_left
        show T.baseChange K * (D.opAlgHom s).baseChange K = (D.opAlgHom s).baseChange K * T.baseChange K
        rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (hTs s).eq]
      rw [map_mul, LinearMap.baseChange_mul, map_add, Module.End.mul_apply, Module.End.mul_apply,
        map_add]
      have e1 : (Th ^ n) ((D.opAlgHom s₁).baseChange K ((D.opAlgHom s₂).baseChange K x)) = 0 := by
        have hsw : (D.opAlgHom s₁).baseChange K ((D.opAlgHom s₂).baseChange K x) =
            (D.opAlgHom s₂).baseChange K ((D.opAlgHom s₁).baseChange K x) := by
          rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, ← map_mul, mul_comm, map_mul,
            LinearMap.baseChange_mul, Module.End.mul_apply]
        rw [hsw, ← Module.End.mul_apply, (hc s₂).eq, Module.End.mul_apply, h₁, map_zero]
      have e2 : (Th ^ n) ((D.opAlgHom s₁).baseChange K ((D.opAlgHom s₂).baseChange K y)) = 0 := by
        rw [← Module.End.mul_apply, (hc s₁).eq, Module.End.mul_apply, h₂, map_zero]
      rw [e1, e2, add_zero]
  obtain ⟨s, hs, hsv⟩ := hall ((1 : K) ⊗ₜ[𝒪] v)

  have hzero : (1 : K) ⊗ₜ[𝒪] (s • (T ^ n) v) = 0 := by
    have h1 : s • (T ^ n) v = D.opAlgHom s ((T ^ n) v) := rfl
    have h2 : D.opAlgHom s ((T ^ n) v) = (T ^ n) (D.opAlgHom s v) := by
      rw [← Module.End.mul_apply, ← ((hTs s).pow_left n).eq, Module.End.mul_apply]
    rw [h1, h2, ← LinearMap.baseChange_tmul, ← LinearMap.baseChange_tmul, LinearMap.baseChange_pow]
    exact hsv
  exact toML_mem_of_smul_mem D ((T ^ n) v) s hs
    (mem_maximalIdeal_smul_of_one_tmul_eq_zero' K hk _ hzero)

end Main

end ResidNilpotence

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    (D : HeckeData 𝒪 V k)

    (Z : Module.End 𝒪 V) (hZ : ∀ g : D.Gen, Z * D.op g = D.op g * Z) (z₀ : D.FreeAlg)

    (K : Type) [Field K] [IsAlgClosed K] [Algebra 𝒪 K] [Algebra k K] [IsScalarTower 𝒪 k K]

    (htest : ∀ (x : K ⊗[𝒪] V) (b : K), x ≠ 0 →
      (∀ g : D.Gen, (D.op g).baseChange K x = algebraMap k K (D.θbar g) • x) →
      Z.baseChange K x = b • x → b = algebraMap k K (D.thetaTilde z₀)) :
    ∃ n : ℕ, ∀ v : V,
      D.toML (((Z - D.opAlgHom z₀) ^ n) v) ∈
        (IsLocalRing.maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 D.ML) :=
  ResidNilpotence.main hk D Z hZ z₀ K htest

end S_CohCarrier_HeckeData_exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector
end P2MW
export P2MW.S_CohCarrier_HeckeData_exists_toML_sub_opAlgHom_pow_mem_of_forall_baseChange_eigenvector (solution)
