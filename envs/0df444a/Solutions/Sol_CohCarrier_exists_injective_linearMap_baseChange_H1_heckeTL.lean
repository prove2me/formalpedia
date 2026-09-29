-- Prove2me | solution 1 for CohCarrier.exists_injective_linearMap_baseChange_H1_heckeTL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b9ba22b6-64d8-5139-b7de-3929a0e229a9

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace C4

section Generic

variable {X : Type*}

theorem linearIndependent_fractionRing {D : Type*} [CommRing D] [IsDomain D]
    (L : Type*) [Field L] [Algebra D L] [IsFractionRing D L]
    {ι : Type*} [Fintype ι] (f : ι → X → D) (hf : LinearIndependent D f) :
    LinearIndependent L (fun i => fun x => algebraMap D L (f i x)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro g hg
  obtain ⟨⟨s, hs⟩, hsg⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors D)
    (Finset.univ.image g)
  have hint : ∀ i, IsLocalization.IsInteger D ((⟨s, hs⟩ : nonZeroDivisors D) • g i) := fun i =>
    hsg (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))
  choose r hr using hint
  have hr' : ∀ i, algebraMap D L (r i) = algebraMap D L s * g i := by
    intro i
    rw [hr i]
    change (s : D) • g i = _
    rw [Algebra.smul_def]
  have hsum : ∀ x, ∑ i, r i * f i x = 0 := by
    intro x
    apply IsFractionRing.injective D L
    rw [map_sum, map_zero]
    have hx := congr_fun hg x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
    calc ∑ i, algebraMap D L (r i * f i x)
        = ∑ i, algebraMap D L s * (g i * algebraMap D L (f i x)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, hr' i, mul_assoc]
      _ = algebraMap D L s * ∑ i, g i * algebraMap D L (f i x) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hx, mul_zero]
  have hr0 : ∀ i, r i = 0 := by
    apply hf
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hsum x
  intro i
  have h := hr' i
  rw [hr0 i, map_zero] at h
  have hs0 : (algebraMap D L s) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  exact (mul_eq_zero.mp h.symm).resolve_left hs0

theorem linearIndependent_extendScalars {L K : Type*} [Field L] [Field K] [Algebra L K]
    {ι : Type*} [Fintype ι] (g : ι → X → L) (hg : LinearIndependent L g) :
    LinearIndependent K (fun i => fun x => algebraMap L K (g i x)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hg ⊢
  intro c hc i
  let b := Module.Basis.ofVectorSpace L K
  refine b.ext_elem fun α => ?_
  rw [map_zero]
  have key : ∀ α, ∑ j, (b.repr (c j) α) • g j = 0 := by
    intro α
    funext x
    have hx := congr_fun hc x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx ⊢
    have := congr_arg (fun y => b.repr y α) hx
    simp only [map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (c j), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  exact hg _ (key α) i

theorem exists_eq_smul_of_forall_dvd {A D : Type*} [AddMonoid A] [CommRing D] [IsDomain D]
    (π : D) (hπ : π ≠ 0) (w : A →+ D) (hw : ∀ x, π ∣ w x) : ∃ w' : A →+ D, w = π • w' := by
  choose f hf using hw
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply mul_left_cancel₀ hπ
    rw [← hf 0, map_zero, mul_zero]
  · intro x y
    apply mul_left_cancel₀ hπ
    rw [mul_add, ← hf, ← hf, ← hf, map_add]
  · ext x
    change w x = π • f x
    rw [smul_eq_mul, hf]

scoped instance noZeroSMulDivisors_addMonoidHom {A : Type*} [AddMonoid A] (D : Type*) [CommRing D]
    [IsDomain D] : NoZeroSMulDivisors D (A →+ D) := by
  refine ⟨fun {c w} h => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    ext x
    have := DFunLike.congr_fun h x
    rw [AddMonoidHom.smul_apply, smul_eq_mul, AddMonoidHom.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left hc

scoped instance isTorsionFree_addMonoidHom {A : Type*} [AddMonoid A] (D : Type*) [CommRing D] :
    Module.IsTorsionFree D (A →+ D) :=
  ⟨fun r hr w w' h => by
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun h x
    simp only [AddMonoidHom.smul_apply, smul_eq_mul] at hx
    exact hr.1 hx⟩

end Generic

section Key

variable {A : Type*} [AddMonoid A]
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
variable {K : Type*} [Field K]

theorem linearIndependent_map_basis (ι : 𝒪 →+* K) {I : Type*} [Fintype I]
    (b : Module.Basis I 𝒪 (A →+ 𝒪)) :
    LinearIndependent K (fun i => fun x : A => ι (b i x)) := by
  classical

  set 𝔭 : Ideal 𝒪 := RingHom.ker ι with h𝔭
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime ι
  set π : 𝒪 := Submodule.IsPrincipal.generator 𝔭 with hπdef
  have h𝔭π : 𝔭 = Ideal.span {π} := (Ideal.span_singleton_generator 𝔭).symm

  let R₀ := 𝒪 ⧸ 𝔭
  let u : I → A → R₀ := fun i x => Ideal.Quotient.mk 𝔭 (b i x)
  have hu : LinearIndependent R₀ u := by
    rw [Fintype.linearIndependent_iff]
    intro gbar hg

    choose g hgg using fun i => Ideal.Quotient.mk_surjective (gbar i)
    have hval : ∀ x, (∑ i, g i * b i x) ∈ 𝔭 := by
      intro x
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      have hx := congr_fun hg x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
      rw [← hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hgg]

    set w : A →+ 𝒪 := ∑ i, g i • b i with hw
    have hwx : ∀ x, w x = ∑ i, g i * b i x := by
      intro x
      rw [hw, AddMonoidHom.finsetSum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [AddMonoidHom.smul_apply, smul_eq_mul]
    have hgoal : ∀ i, g i ∈ 𝔭 := by
      by_cases hπ : π = 0
      ·
        have h0 : w = 0 := by
          ext x
          have := hval x
          rw [h𝔭π, hπ, Ideal.mem_span_singleton, zero_dvd_iff] at this
          rw [hwx, AddMonoidHom.zero_apply]
          exact this
        have hli := Fintype.linearIndependent_iff.mp b.linearIndependent g (by rw [← hw, h0])
        intro i
        rw [hli i]
        exact zero_mem _
      · obtain ⟨w', hw'⟩ := exists_eq_smul_of_forall_dvd π hπ w fun x => by
          rw [← Ideal.mem_span_singleton, ← h𝔭π, hwx]
          exact hval x

        have hrel : ∑ i, (g i - π * b.repr w' i) • b i = 0 := by
          simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
          rw [← hw, ← Finset.smul_sum, b.sum_repr w', hw', sub_self]
        have hli := Fintype.linearIndependent_iff.mp b.linearIndependent _ hrel
        intro i
        have : g i = π * b.repr w' i := sub_eq_zero.mp (hli i)
        rw [this, h𝔭π]
        exact Ideal.mem_span_singleton.mpr (dvd_mul_right π _)
    intro i
    rw [← hgg i]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hgoal i)

  let ιbar : R₀ →+* K := Ideal.Quotient.lift 𝔭 ι fun a ha => ha
  have hιbar : Function.Injective ιbar := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let L := FractionRing R₀
  let lK : L →+* K := IsFractionRing.lift hιbar
  letI : Algebra L K := lK.toAlgebra
  have h1 := linearIndependent_fractionRing L u hu
  have h2 := linearIndependent_extendScalars (K := K) _ h1
  have heq : (fun i => fun x : A => algebraMap L K (algebraMap R₀ L (u i x))) =
      fun i => fun x : A => ι (b i x) := by
    funext i x
    change lK (algebraMap R₀ L (Ideal.Quotient.mk 𝔭 (b i x))) = ι (b i x)
    rw [IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]
  rw [heq] at h2
  exact h2

end Key

end C4
p2m_reactivate "P2MW.S_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL.C4"

open CohCarrier in

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] :
    ∃ j : K ⊗[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[K] CohCarrier.H1 M H K,
      Function.Injective j ∧
      (∀ (c : K) (w : CohCarrier.H1 M H 𝒪),
        j (c ⊗ₜ[𝒪] w) = c • ((algebraMap 𝒪 K).toAddMonoidHom.comp w)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (x : K ⊗[𝒪] CohCarrier.H1 M H 𝒪),
        j (((CohCarrier.heckeTL M H 𝒪 ℓ).baseChange K) x) =
          CohCarrier.heckeTL M H K ℓ (j x) := by
  classical
  let ι : 𝒪 →+* K := algebraMap 𝒪 K

  let J : H1 M H 𝒪 →ₗ[𝒪] H1 M H K :=
    { toFun := fun w => ι.toAddMonoidHom.comp w
      map_add' := fun w w' => DFunLike.ext _ _ fun x => map_add ι (w x) (w' x)
      map_smul' := fun r w => DFunLike.ext _ _ fun x => by
        change ι (r * w x) = r • ι (w x)
        rw [map_mul, Algebra.smul_def] }

  let φ : K →ₗ[K] (H1 M H 𝒪 →ₗ[𝒪] H1 M H K) :=
    { toFun := fun c => c • J
      map_add' := fun a b => add_smul a b J
      map_smul' := fun a c => mul_smul a c J }
  let j : K ⊗[𝒪] H1 M H 𝒪 →ₗ[K] H1 M H K := TensorProduct.AlgebraTensorModule.lift φ
  have hj : ∀ (c : K) (w : H1 M H 𝒪), j (c ⊗ₜ[𝒪] w) = c • (ι.toAddMonoidHom.comp w) := by
    intro c w
    change TensorProduct.AlgebraTensorModule.lift φ (c ⊗ₜ[𝒪] w) = _
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    rfl
  refine ⟨j, ?_, hj, ?_⟩
  ·
    haveI : Module.Finite 𝒪 (H1 M H 𝒪) := CohCarrier.H1_moduleFinite M H 𝒪 𝒪
    haveI : Module.IsTorsionFree 𝒪 (H1 M H 𝒪) :=
      C4.isTorsionFree_addMonoidHom (A := Additive ↥(GammaH M H)) 𝒪
    haveI : Module.Free 𝒪 (H1 M H 𝒪) := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis 𝒪 (H1 M H 𝒪)
    let bK := Algebra.TensorProduct.basis K b

    have hbK : ∀ i, j (bK i) = ι.toAddMonoidHom.comp (b i) := by
      intro i
      change j (Algebra.TensorProduct.basis K b i) = _
      rw [Algebra.TensorProduct.basis_apply, hj, one_smul]
    have hF : LinearIndependent K (fun i => j (bK i)) := by
      have hcoe : LinearIndependent K (fun i => fun x : Additive ↥(GammaH M H) => ι (b i x)) :=
        C4.linearIndependent_map_basis (A := Additive ↥(GammaH M H)) ι b
      let coeL : H1 M H K →ₗ[K] (Additive ↥(GammaH M H) → K) :=
        { toFun := fun w => ⇑w, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      refine LinearIndependent.of_comp coeL ?_
      have heq : (coeL ∘ fun i => j (bK i)) = fun i => fun x => ι (b i x) := by
        funext i x
        change (j (bK i)) x = ι (b i x)
        rw [hbK i]
        rfl
      rw [heq]
      exact hcoe
    refine (injective_iff_map_eq_zero j).mpr fun x hx => ?_
    have hsum : ∑ i, (bK.repr x i) • j (bK i) = 0 := by
      have h0 : j (∑ i, bK.repr x i • bK i) = 0 := by rw [bK.sum_repr]; exact hx
      simpa only [map_sum, map_smul] using h0
    have hc := Fintype.linearIndependent_iff.mp hF (fun i => bK.repr x i) hsum
    rw [← bK.sum_repr x]
    exact Finset.sum_eq_zero fun i _ => by rw [show bK.repr x i = 0 from hc i, zero_smul]
  ·
    intro ℓ _ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c w =>
        rw [LinearMap.baseChange_tmul, hj, hj, map_smul]
        congr 1
        rw [heckeTL_apply, heckeTL_apply]
        exact (CohCarrier.heckeT_comp_coeff M H ℓ ι.toAddMonoidHom w).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end S_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL
end P2MW
export P2MW.S_CohCarrier_exists_injective_linearMap_baseChange_H1_heckeTL (solution)
