-- Prove2me | solution 1 for GaloisRep.DeformationRingData.ker_algHom_eq_span_of_relaxed_strictOrdinary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3430852f-8e3a-585d-99f2-775ce80660b9

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Theorems.Thm_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient
import Theorems.Thm_GaloisRepAdic_strictOrdinaryCondition_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong
import Theorems.Thm_GaloisRep_DeformationRingData_algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_ker_algHom_eq_span_of_relaxed_strictOrdinary
set_option autoImplicit false
open IsLocalRing Polynomial

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace TWLocSO

section Naturality

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T]
  {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem cancel_naturality (φ : V →ₗ[R] W) (x : T ⊗[S] (S ⊗[R] V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W ((φ.baseChange S).baseChange T x) =
      φ.baseChange T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cancel_symm_naturality (φ : V →ₗ[R] W) (y : T ⊗[R] V) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T W).symm (φ.baseChange T y) =
      (φ.baseChange S).baseChange T
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V).symm y) := by
  rw [LinearEquiv.symm_apply_eq, cancel_naturality, LinearEquiv.apply_symm_apply]

end Naturality

section Adic

variable {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [CommRing C] [IsLocalRing C]

noncomputable def bcComp (ρ : GaloisRepAdic A) (f : A →+* B) (hf : IsLocalHom f)
    (g : B →+* C) (hg : IsLocalHom g) (hgf : IsLocalHom (g.comp f)) :
    GaloisRepAdic.Equiv ((ρ.baseChangeAlong f hf).baseChangeAlong g hg)
      (ρ.baseChangeAlong (g.comp f) hgf) :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra B C := g.toAlgebra
  letI : Algebra A C := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
    map_apply := fun σ x => by
      change TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
          ((((ρ.ρ σ).baseChange B).baseChange C) x) =
        ((ρ.ρ σ).baseChange C) (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x)
      exact cancel_naturality (ρ.ρ σ) x }

noncomputable def bcId (ρ : GaloisRepAdic A) (h : IsLocalHom (RingHom.id A)) :
    GaloisRepAdic.Equiv (ρ.baseChangeAlong (RingHom.id A) h) ρ :=
  letI : Algebra A A := (RingHom.id A).toAlgebra
  { toLinearEquiv := TensorProduct.lid A ρ.V
    map_apply := fun σ x => by
      change TensorProduct.lid A ρ.V (((ρ.ρ σ).baseChange A) x) = ρ.ρ σ (TensorProduct.lid A ρ.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a v => simp only [LinearMap.baseChange_tmul, TensorProduct.lid_tmul, map_smul]
      | add x y hx hy => simp only [map_add, hx, hy] }

theorem isEquiv_bc_congr (ρ : GaloisRepAdic A) {f g : A →+* B} (hfg : f = g)
    (hf : IsLocalHom f) (hg : IsLocalHom g) :
    (ρ.baseChangeAlong f hf).IsEquiv (ρ.baseChangeAlong g hg) := by
  subst hfg
  exact ⟨GaloisRepAdic.Equiv.refl _⟩

theorem isEquiv_trans {ρ₁ ρ₂ ρ₃ : GaloisRepAdic A} (h₁ : ρ₁.IsEquiv ρ₂) (h₂ : ρ₂.IsEquiv ρ₃) :
    ρ₁.IsEquiv ρ₃ := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

theorem isEquiv_symm {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂) : ρ₂.IsEquiv ρ₁ := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem isEquiv_bc {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂) (f : A →+* B) (hf : IsLocalHom f) :
    (ρ₁.baseChangeAlong f hf).IsEquiv (ρ₂.baseChangeAlong f hf) := by
  obtain ⟨e⟩ := h
  exact ⟨e.baseChangeAlong f hf⟩

noncomputable def residualBC (ρ : GaloisRepAdic A) (f : A →+* B) (hf : IsLocalHom f) :
    ResidualGaloisRep.Equiv (ρ.baseChangeAlong f hf).residual
      (ρ.residual.baseChangeAlong (@ResidueField.map A B _ _ _ _ f hf)) :=
  haveI := hf
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map f).toAlgebra
  letI : Module (ResidueField A) (ResidueField B) := Algebra.toModule
  letI : Module A (ResidueField B) := Algebra.toModule
  haveI : IsScalarTower A (ResidueField A) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
          ρ.V).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
          (ResidueField B) ρ.V).symm
    map_apply := fun σ x => by
      change ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
            ρ.V ((((ρ.ρ σ).baseChange B).baseChange (ResidueField B)) x))) =
        ((ρ.ρ σ).baseChange (ResidueField A)).baseChange (ResidueField B)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B)
            ρ.V x))
      exact (congrArg ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
            (ResidueField B) (ResidueField B) ρ.V).symm) (cancel_naturality (ρ.ρ σ) x)).trans
        (cancel_symm_naturality (ρ.ρ σ) _) }

end Adic

section Residual

variable {k k' k'' : Type} [Field k] [Field k'] [Field k'']

noncomputable def rbcComp (ρ : ResidualGaloisRep k) (f : k →+* k') (g : k' →+* k'') :
    ResidualGaloisRep.Equiv ((ρ.baseChangeAlong f).baseChangeAlong g)
      (ρ.baseChangeAlong (g.comp f)) :=
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k' k'' := g.toAlgebra
  letI : Algebra k k'' := (g.comp f).toAlgebra
  haveI : IsScalarTower k k' k'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  { toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
    map_apply := fun σ x => by
      change TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V
          ((((ρ.ρ σ).baseChange k').baseChange k'') x) =
        ((ρ.ρ σ).baseChange k'') (TensorProduct.AlgebraTensorModule.cancelBaseChange k k' k'' k'' ρ.V x)
      exact cancel_naturality (ρ.ρ σ) x }

theorem risEquiv_congr (ρ : ResidualGaloisRep k) {f g : k →+* k'} (hfg : ∀ x, f x = g x) :
    (ρ.baseChangeAlong f).IsEquiv (ρ.baseChangeAlong g) := by
  obtain rfl : f = g := RingHom.ext hfg
  exact ⟨ResidualGaloisRep.Equiv.refl _⟩

theorem risEquiv_trans {ρ₁ ρ₂ ρ₃ : ResidualGaloisRep k} (h₁ : ρ₁.IsEquiv ρ₂) (h₂ : ρ₂.IsEquiv ρ₃) :
    ρ₁.IsEquiv ρ₃ := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩

end Residual

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

end TWLocSO

namespace TWBridgesSO

theorem baseChangeAlong_isUnramifiedAt_of_forall_algHom_inertiaCharacter_eq_one
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (DQ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    {p q k : ℕ}
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (πΔ : (ZMod q)ˣ →* Multiplicative (ZMod (p ^ k)))
    (χ : Multiplicative (ZMod (p ^ k)) →* DQ.Rˣ)
    (hχ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∃ b : Module.Basis (Fin 2) DQ.R DQ.ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        DQ.ρ.ρ σ (b 0) = ((χ (πΔ (cyc σ)) : DQ.Rˣ) : DQ.R) • b 0 ∧
        DQ.ρ.ρ σ (b 1) = (((χ (πΔ (cyc σ)))⁻¹ : DQ.Rˣ) : DQ.R) • b 1)
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (f : DQ.R →ₐ[𝒪] B) (hf : IsLocalHom (f : DQ.R →+* B))
    (hfχ : ∀ d : Multiplicative (ZMod (p ^ k)), f ((χ d : DQ.Rˣ) : DQ.R) = 1) :
    (DQ.ρ.baseChangeAlong (f : DQ.R →+* B) hf).IsUnramifiedAt q := by
  intro P hP σ hσ
  obtain ⟨b, hb⟩ := hχ P hP
  letI : Algebra DQ.R B := (f : DQ.R →+* B).toAlgebra
  show (DQ.ρ.ρ σ).baseChange B = 1
  have hone : ∀ a : DQ.R, f a = 1 → ∀ v : DQ.ρ.V,
      (1 : B) ⊗ₜ[DQ.R] (a • v) = (1 : B) ⊗ₜ[DQ.R] v := by
    intro a ha v
    rw [TensorProduct.tmul_smul, ← algebraMap_smul B a ((1 : B) ⊗ₜ[DQ.R] v),
      show (algebraMap DQ.R B) a = 1 from ha, one_smul]
  refine (Algebra.TensorProduct.basis B b).ext fun i => ?_
  rw [Algebra.TensorProduct.basis_apply, Module.End.one_apply, LinearMap.baseChange_tmul]
  fin_cases i
  · show (1 : B) ⊗ₜ[DQ.R] (DQ.ρ.ρ σ) (b 0) = (1 : B) ⊗ₜ[DQ.R] b 0
    rw [(hb σ hσ).1]
    exact hone _ (hfχ _) _
  · show (1 : B) ⊗ₜ[DQ.R] (DQ.ρ.ρ σ) (b 1) = (1 : B) ⊗ₜ[DQ.R] b 1
    rw [(hb σ hσ).2]
    refine hone _ ?_ _
    have h1 : (((χ (πΔ (cyc σ)))⁻¹ : DQ.Rˣ) : DQ.R)
        = ((χ ((πΔ (cyc σ))⁻¹) : DQ.Rˣ) : DQ.R) := by
      rw [map_inv]
    rw [h1]
    exact hfχ _

theorem algHom_eq_of_baseChangeAlong_isEquiv
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (DQ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B] [Algebra 𝒪 B] [IsLocalHom (algebraMap 𝒪 B)]
    (hBres : Function.Surjective (residue B ∘ algebraMap 𝒪 B))
    (ρB : GaloisRepAdic B) (h𝒟B : 𝒟 ρB)
    (hresB : ρB.residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 B))))
    (g₁ g₂ : DQ.R →ₐ[𝒪] B)
    (hg₁ : IsLocalHom (g₁ : DQ.R →+* B)) (hg₂ : IsLocalHom (g₂ : DQ.R →+* B))
    (hg₁ρ : (DQ.ρ.baseChangeAlong (g₁ : DQ.R →+* B) hg₁).IsEquiv ρB)
    (hg₂ρ : (DQ.ρ.baseChangeAlong (g₂ : DQ.R →+* B) hg₂).IsEquiv ρB) :
    g₁ = g₂ := by
  obtain ⟨φ, -, huniq⟩ := DQ.universal B hBres ρB h𝒟B hresB
  exact (huniq g₁ ⟨hg₁, hg₁ρ⟩).trans (huniq g₂ ⟨hg₂, hg₂ρ⟩).symm

end TWBridgesSO

open TWLocSO TWBridgesSO in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) (Smin Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q ∉ Smin) {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    (Dmin : GaloisRep.DeformationRingData 𝒪 ρbar (GaloisRep.minimalStrictOrdinaryCondition 𝒪 p Smin))
    (DQ : GaloisRep.DeformationRingData 𝒪 ρbar (fun _A _ _ _ ρ =>
        GaloisRep.strictOrdinaryCondition 𝒪 p (Smin ∪ Q) ρ ∧
          ∀ q ∈ Smin, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q))
    (ε : DQ.R →ₐ[𝒪] Dmin.R) (hε : IsLocalHom (ε : DQ.R →+* Dmin.R))
    (hερ : (DQ.ρ.baseChangeAlong (ε : DQ.R →+* Dmin.R) hε).IsEquiv Dmin.ρ)
    (k : ℕ → ℕ)
    (cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ))
    (hcyc : ∀ q ∈ Q, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc q σ : ZMod q).val))
    (πΔ : (q : ℕ) → ((ZMod q)ˣ →* Multiplicative (ZMod (p ^ k q))))
    (hπΔ : ∀ q ∈ Q, Function.Surjective (πΔ q))
    (χ : (q : ℕ) → (Multiplicative (ZMod (p ^ k q)) →* DQ.Rˣ))
    (hχ : ∀ q ∈ Q, ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
      ∃ b : Module.Basis (Fin 2) DQ.R DQ.ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        DQ.ρ.ρ σ (b 0) = ((χ q (πΔ q (cyc q σ)) : DQ.Rˣ) : DQ.R) • b 0 ∧
        DQ.ρ.ρ σ (b 1) = (((χ q (πΔ q (cyc q σ)))⁻¹ : DQ.Rˣ) : DQ.R) • b 1)
    (ι : MonoidAlgebra 𝒪 (Π q : Q, Multiplicative (ZMod (p ^ k q))) →ₐ[𝒪] DQ.R)
    (hι : ∀ g : (Π q : Q, Multiplicative (ZMod (p ^ k q))),
      ι (MonoidAlgebra.of 𝒪 _ g) = ∏ q : Q, ((χ q (g q) : DQ.Rˣ) : DQ.R)) :
    RingHom.ker (ε : DQ.R →+* Dmin.R) =
      Ideal.span (Set.range fun g : (Π q : Q, Multiplicative (ZMod (p ^ k q))) => ι (MonoidAlgebra.of 𝒪 _ g) - 1) := by
  classical
  have hεχ : ∀ q ∈ Q, ∀ d : Multiplicative (ZMod (p ^ k q)),
      ε ((χ q d : DQ.Rˣ) : DQ.R) = 1 := fun q hq d =>
    GaloisRep.DeformationRingData.algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt
      p Dmin DQ (hQ q hq).1 (fun _A _ _ _ ρ hρ => hρ.1.2.2 q (hQ q hq).1 (hQ q hq).2) ε hε hερ
      (cyc q) (hcyc q hq) (πΔ q) (hπΔ q hq) (χ q) (hχ q hq) d
  set J : Ideal DQ.R :=
    Ideal.span (Set.range fun g : (Π q : Q, Multiplicative (ZMod (p ^ k q))) =>
      ι (MonoidAlgebra.of 𝒪 _ g) - 1) with hJdef

  have hJker : J ≤ RingHom.ker (ε : DQ.R →+* Dmin.R) := by
    rw [hJdef, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hι, map_prod]
    have h1 : ∀ q : Q, (ε : DQ.R →+* Dmin.R) ((χ q.1 (g q) : DQ.Rˣ) : DQ.R) = 1 :=
      fun q => hεχ q.1 q.2 (g q)
    rw [Finset.prod_congr rfl fun q _ => h1 q, Finset.prod_const_one]
    exact sub_self 1

  have hχJ : ∀ q (hqQ : q ∈ Q) (d : Multiplicative (ZMod (p ^ k q))),
      ((χ q d : DQ.Rˣ) : DQ.R) - 1 ∈ J := by
    intro q hqQ d
    have hsingle : ((χ q d : DQ.Rˣ) : DQ.R)
        = ι (MonoidAlgebra.of 𝒪 _ (Pi.mulSingle (⟨q, hqQ⟩ : Q) d)) := by
      rw [hι]
      rw [Finset.prod_eq_single (⟨q, hqQ⟩ : Q)]
      · rw [Pi.mulSingle_eq_same]
      · intro q' _ hne
        rw [Pi.mulSingle_eq_of_ne hne, map_one, Units.val_one]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    rw [hsingle]
    exact Ideal.subset_span ⟨_, rfl⟩

  refine le_antisymm (fun x hx => ?_) hJker
  have hJne : J ≠ ⊤ := by
    intro h
    have h1 : (1 : DQ.R) ∈ J := h ▸ Submodule.mem_top
    have h2 := hJker h1
    rw [RingHom.mem_ker, map_one] at h2
    exact one_ne_zero h2

  haveI : Nontrivial (DQ.R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  haveI : IsLocalRing (DQ.R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsAdicComplete (maximalIdeal (DQ.R ⧸ J)) (DQ.R ⧸ J) := by
    have h := IsLocalRing.isAdicComplete_map_maximalIdeal_quotient (R := DQ.R) J
    rwa [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  haveI hmkloc : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (algebraMap 𝒪 (DQ.R ⧸ J)) := by
    change IsLocalHom ((Ideal.Quotient.mk J).comp (algebraMap 𝒪 DQ.R))
    exact RingHom.isLocalHom_comp _ _
  have hresQ : Function.Surjective
      (residue (DQ.R ⧸ J) ∘ algebraMap 𝒪 (DQ.R ⧸ J)) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨o, ho⟩ := DQ.residue_surjective (residue DQ.R a)
    refine ⟨o, ?_⟩
    simp only [Function.comp_apply] at ho ⊢
    change residue _ (Ideal.Quotient.mk J (algebraMap 𝒪 DQ.R o)) =
      residue _ (Ideal.Quotient.mk J a)
    rw [← ResidueField.map_residue (Ideal.Quotient.mk J),
      ← ResidueField.map_residue (Ideal.Quotient.mk J), ho]

  let π : DQ.R →ₐ[𝒪] DQ.R ⧸ J := Ideal.Quotient.mkₐ 𝒪 J
  have hπsurj : Function.Surjective π := Ideal.Quotient.mkₐ_surjective 𝒪 _
  haveI hπloc : IsLocalHom (π : DQ.R →+* DQ.R ⧸ J) := IsLocalHom.of_surjective _ hπsurj
  set ρA : GaloisRepAdic (DQ.R ⧸ J) :=
    DQ.ρ.baseChangeAlong (π : DQ.R →+* DQ.R ⧸ J) hπloc with hρAdef
  have h𝒟ρA : GaloisRep.strictOrdinaryCondition 𝒪 p (Smin ∪ Q) ρA ∧
      ∀ q ∈ Smin, q.Prime → q ≠ p → ρA.IsUnipotentOnInertiaAt q := by
    constructor
    · exact GaloisRepAdic.strictOrdinaryCondition_baseChangeAlong 𝒪 _ hπloc DQ.ρ DQ.isOfType.1
    · intro q hq hqp hqne
      exact GaloisRepAdic.isUnipotentOnInertiaAt_baseChangeAlong _ hπloc DQ.ρ
        (DQ.isOfType.2 q hq hqp hqne)

  have hmin : GaloisRep.minimalStrictOrdinaryCondition 𝒪 p Smin ρA := by
    refine ⟨⟨h𝒟ρA.1.1, h𝒟ρA.1.2.1, ?_⟩, h𝒟ρA.2⟩
    intro q' hq' hq'S
    by_cases hq'Q : q' ∈ Q
    · exact baseChangeAlong_isUnramifiedAt_of_forall_algHom_inertiaCharacter_eq_one
        DQ (cyc q') (πΔ q') (χ q') (hχ q' hq'Q) π hπloc (fun d => by
          have h1 := hχJ q' hq'Q d
          have h2 : Ideal.Quotient.mk J (((χ q' d : DQ.Rˣ) : DQ.R) - 1) = 0 :=
            (Ideal.Quotient.eq_zero_iff_mem).mpr h1
          rw [map_sub, map_one, sub_eq_zero] at h2
          exact h2)
    · refine h𝒟ρA.1.2.2 q' hq' ?_
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hq'S h
      · exact hq'Q h

  have hres' : ρA.residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 (DQ.R ⧸ J)))) := by
    refine risEquiv_trans ⟨residualBC DQ.ρ _ hπloc⟩ ?_
    obtain ⟨e⟩ := DQ.residual_isEquiv
    refine risEquiv_trans ⟨e.baseChangeAlong _⟩ ?_
    refine risEquiv_trans ⟨rbcComp ρbar _ _⟩ (risEquiv_congr ρbar fun y => ?_)
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    rfl

  obtain ⟨ψ, ⟨hψloc, hψρ⟩, -⟩ := Dmin.universal (DQ.R ⧸ J) hresQ ρA hmin hres'

  have hcomploc : IsLocalHom ((ψ.comp ε : DQ.R →ₐ[𝒪] DQ.R ⧸ J) : DQ.R →+* DQ.R ⧸ J) := by
    change IsLocalHom ((ψ : Dmin.R →+* DQ.R ⧸ J).comp (ε : DQ.R →+* Dmin.R))
    exact RingHom.isLocalHom_comp _ _
  have hcomploc2 : IsLocalHom ((ψ : Dmin.R →+* DQ.R ⧸ J).comp (ε : DQ.R →+* Dmin.R)) :=
    RingHom.isLocalHom_comp _ _
  have hcompρ : (DQ.ρ.baseChangeAlong
      ((ψ.comp ε : DQ.R →ₐ[𝒪] DQ.R ⧸ J) : DQ.R →+* DQ.R ⧸ J) hcomploc).IsEquiv ρA := by
    refine isEquiv_trans (isEquiv_bc_congr DQ.ρ
      (show ((ψ.comp ε : DQ.R →ₐ[𝒪] DQ.R ⧸ J) : DQ.R →+* DQ.R ⧸ J)
          = (ψ : Dmin.R →+* DQ.R ⧸ J).comp (ε : DQ.R →+* Dmin.R) from rfl)
      hcomploc hcomploc2) ?_
    refine isEquiv_trans (isEquiv_symm ⟨bcComp DQ.ρ _ hε _ hψloc hcomploc2⟩) ?_
    exact isEquiv_trans (isEquiv_bc hερ (ψ : Dmin.R →+* DQ.R ⧸ J) hψloc) hψρ
  have hπρ : (DQ.ρ.baseChangeAlong (π : DQ.R →+* DQ.R ⧸ J) hπloc).IsEquiv ρA := by
    rw [hρAdef]
    exact ⟨GaloisRepAdic.Equiv.refl _⟩
  have heq : ψ.comp ε = π :=
    algHom_eq_of_baseChangeAlong_isEquiv DQ hresQ ρA h𝒟ρA hres'
      (ψ.comp ε) π hcomploc hπloc hcompρ hπρ

  rw [RingHom.mem_ker] at hx
  have h1 : π x = 0 := by
    rw [← heq]
    show ψ (ε x) = 0
    have hx' : ε x = 0 := hx
    rw [hx', map_zero]
  have h2 : Ideal.Quotient.mk J x = 0 := h1
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h2

end

end S_GaloisRep_DeformationRingData_ker_algHom_eq_span_of_relaxed_strictOrdinary
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_ker_algHom_eq_span_of_relaxed_strictOrdinary (solution)
