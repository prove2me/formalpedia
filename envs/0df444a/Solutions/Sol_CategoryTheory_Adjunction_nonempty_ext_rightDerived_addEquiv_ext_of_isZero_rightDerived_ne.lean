-- Prove2me | solution 1 for CategoryTheory.Adjunction.nonempty_ext_rightDerived_addEquiv_ext_of_isZero_rightDerived_ne
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-26T09:33:59.378389+00:00
-- url     : https://prove2.me/submissions/6a2a5f07-311a-49d0-89a1-ac8e43a38d5b

import Mathlib

set_option autoImplicit false

universe w v v' u u'

open CategoryTheory Limits Abelian

noncomputable section

-- inlined from S4-EtLeray Edge
namespace RamanujanPetersson.EtLeray


variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasExt.{w} C] [HasExt.{w} D]
variable {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- **The Leray edge map** `Ext^n(A, R N) → Ext^n(L A, N)`, `x ↦ L(x) ∘ mk₀ ε_N`. -/
def edge (A : D) (N : C) (n : ℕ) : Ext A (R.obj N) n →+ Ext (L.obj A) N n where
  toFun x := (x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app N)) (add_zero n)
  map_zero' := by simp [Ext.mapExactFunctor_zero]
  map_add' x y := by simp [Ext.mapExactFunctor_add]

theorem edge_apply (A : D) (N : C) (n : ℕ) (x : Ext A (R.obj N) n) :
    edge adj A N n x = (x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app N)) (add_zero n) :=
  rfl

theorem edge_mk₀ (A : D) (N : C) (g : A ⟶ R.obj N) :
    edge adj A N 0 (Ext.mk₀ g) = Ext.mk₀ ((adj.homEquiv A N).symm g) := by
  rw [edge_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Adjunction.homEquiv_counit]

theorem edge_zero_bijective (A : D) (N : C) : Function.Bijective (edge adj A N 0) := by
  have h : (edge adj A N 0 : Ext A (R.obj N) 0 → Ext (L.obj A) N 0) =
      Ext.mk₀ ∘ (adj.homEquiv A N).symm ∘ Ext.homEquiv₀ := by
    funext x
    obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective A (R.obj N)).2 x
    simp only [Function.comp_apply, edge_mk₀]
    congr 2
    exact (Ext.homEquiv₀.apply_symm_apply y).symm
  rw [h]
  exact (Ext.mk₀_bijective _ _).comp ((adj.homEquiv A N).symm.bijective.comp Ext.homEquiv₀.bijective)

theorem edge_comp_mk₀ (A : D) {N N' : C} (h : N ⟶ N') {n : ℕ} (x : Ext A (R.obj N) n) :
    edge adj A N' n (x.comp (Ext.mk₀ (R.map h)) (add_zero n)) =
      (edge adj A N n x).comp (Ext.mk₀ h) (add_zero n) := by
  simp only [edge_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc _ _ _ (add_zero n) (add_zero 0) (by simp),
    Ext.comp_assoc _ _ _ (add_zero n) (add_zero 0) (by simp), Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg (fun f => (Ext.mapExactFunctor L x).comp (Ext.mk₀ f) (add_zero n)) (adj.counit_naturality h)

variable [R.Additive]

/-- The counit as a morphism of short complexes `L R S ⟶ S`. -/
@[simps]
def counitSC (S : ShortComplex C) : (S.map R).map L ⟶ S where
  τ₁ := adj.counit.app S.X₁
  τ₂ := adj.counit.app S.X₂
  τ₃ := adj.counit.app S.X₃
  comm₁₂ := (adj.counit_naturality S.f).symm
  comm₂₃ := (adj.counit_naturality S.g).symm

set_option backward.isDefEq.respectTransparency false in
theorem edge_comp_extClass (A : D) {S : ShortComplex C} (hS : S.ShortExact) (hRS : (S.map R).ShortExact)
    {n : ℕ} (x : Ext A (S.map R).X₃ n) :
    edge adj A S.X₁ (n + 1) (x.comp hRS.extClass rfl) = (edge adj A S.X₃ n x).comp hS.extClass rfl := by
  have hn := (hRS.map_of_exact L).extClass_naturality hS (counitSC adj S)
  simp only [counitSC_τ₁, counitSC_τ₃] at hn
  rw [edge_apply, edge_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.comp_assoc (x.mapExactFunctor L) (hRS.map_of_exact L).extClass
      (Ext.mk₀ (adj.counit.app S.X₁)) rfl (add_zero 1) (by omega), hn,
    ← Ext.comp_assoc (x.mapExactFunctor L) (Ext.mk₀ (adj.counit.app S.X₃)) hS.extClass
      (add_zero n) (zero_add 1) (by omega)]

end RamanujanPetersson.EtLeray

-- inlined from S4-EtLeray Shift
namespace RamanujanPetersson.EtLeray


variable {C : Type u} [Category.{v} C] [Abelian C]
variable {N : C} (P : InjectiveResolution N)

/-- `Qc P = coker(N → P⁰)`. -/
abbrev Qc : C := cokernel (P.ι.f 0)

/-- The short exact sequence `N → P⁰ → Qc P`. -/
abbrev presQ : ShortComplex C := ShortComplex.mk (P.ι.f 0) (cokernel.π (P.ι.f 0)) (cokernel.condition _)

theorem presQ_shortExact : (presQ P).ShortExact where
  exact := ShortComplex.exact_cokernel (P.ι.f 0)

/-- `Qc P ↪ P¹`. -/
def dQ : Qc P ⟶ P.cocomplex.X 1 := cokernel.desc _ (P.cocomplex.d 0 1) P.ι_f_zero_comp_complex_d

@[reassoc (attr := simp)]
theorem π_dQ : cokernel.π (P.ι.f 0) ≫ dQ P = P.cocomplex.d 0 1 := cokernel.π_desc _ _ _

instance mono_dQ : Mono (dQ P) := P.exact₀.mono_cokernelDesc

/-- The shifted complex `P^(•+1)`. -/
def shCx : CochainComplex C ℕ :=
  CochainComplex.of (fun q => P.cocomplex.X (q + 1)) (fun q => P.cocomplex.d (q + 1) (q + 2))
    (fun _ => P.cocomplex.d_comp_d _ _ _)

theorem shCx_d (q : ℕ) : (shCx P).d q (q + 1) = P.cocomplex.d (q + 1) (q + 2) := by
  simp [shCx]

theorem shCx_d' (q : ℕ) : (shCx P).d (q + 1) (q + 2) = P.cocomplex.d (q + 2) (q + 3) :=
  shCx_d P (q + 1)

theorem shCx_d01 : (shCx P).d 0 1 = P.cocomplex.d 1 2 := shCx_d P 0

theorem dQ_d12 : dQ P ≫ P.cocomplex.d 1 2 = 0 := by
  rw [← cancel_epi (cokernel.π (P.ι.f 0)), π_dQ_assoc, HomologicalComplex.d_comp_d, comp_zero]

theorem dQ_d : dQ P ≫ (shCx P).d 0 1 = 0 :=
  (congrArg (fun g => dQ P ≫ g) (shCx_d01 P)).trans (dQ_d12 P)

/-- `Qc P → P¹ → P²` is exact. -/
theorem shExact₀ : (ShortComplex.mk (dQ P) (P.cocomplex.d 1 2) (dQ_d12 P)).Exact := by
  have h : (ShortComplex.mk (P.cocomplex.d 0 1) (P.cocomplex.d 1 2)
      (P.cocomplex.d_comp_d 0 1 2)).Exact := P.exact_succ 0
  let φ : ShortComplex.mk (P.cocomplex.d 0 1) (P.cocomplex.d 1 2) (P.cocomplex.d_comp_d 0 1 2) ⟶
      ShortComplex.mk (dQ P) (P.cocomplex.d 1 2) (dQ_d12 P) :=
    { τ₁ := cokernel.π (P.ι.f 0)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (π_dQ P).trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := (inferInstance : Epi (cokernel.π (P.ι.f 0)))
  have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 (P.cocomplex.X 1)))
  have : Mono φ.τ₃ := (inferInstance : Mono (𝟙 (P.cocomplex.X 2)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h

theorem shCx_exactAt_succ (n : ℕ) : (shCx P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)]
  refine (ShortComplex.exact_iff_of_iso ?_).2 (P.exact_succ (n + 1))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((shCx_d P n).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((shCx_d' P n).symm.trans (Category.comp_id _).symm))

set_option backward.isDefEq.respectTransparency false in
theorem ι_f0 : ((CochainComplex.fromSingle₀Equiv (shCx P) (Qc P)).symm ⟨dQ P, dQ_d P⟩).f 0 = dQ P :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The shifted injective resolution** of `Qc P`. -/
def shRes : InjectiveResolution (Qc P) where
  cocomplex := shCx P
  injective q := P.injective (q + 1)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨dQ P, dQ_d P⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨shExact₀ P, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans ((ι_f0 P).symm.trans (Category.comp_id _).symm))
          (by simp [shCx_d01])
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt]
      · exact shCx_exactAt_succ P _
      · apply CochainComplex.exactAt_succ_single_obj⟩

theorem shRes_cocomplex : (shRes P).cocomplex = shCx P := rfl

variable [HasInjectiveResolutions C] {D : Type u'} [Category.{v'} D] [Abelian D] (R : C ⥤ D) [R.Additive]

/-- The short complexes computing `R^(q+1)(Qc P)` and `R^(q+2) N` agree. -/
def scIso (q : ℕ) :
    ((R.mapHomologicalComplex _).obj (shCx P)).sc' q (q + 1) (q + 2) ≅
      ((R.mapHomologicalComplex _).obj P.cocomplex).sc' (q + 1) (q + 2) (q + 3) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [shCx_d] <;> exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by simp [shCx_d'] <;> exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Dimension shift**: `R^(q+1)(Qc P) ≅ R^(q+2) N`. -/
def dsIso (q : ℕ) : (R.rightDerived (q + 1)).obj (Qc P) ≅ (R.rightDerived (q + 2)).obj N :=
  (shRes P).isoRightDerivedObj R (q + 1) ≪≫
    ((R.mapHomologicalComplex _).obj (shCx P)).homologyIsoSc' q (q + 1) (q + 2) (by simp)
      (by simp only [CochainComplex.next]; rfl) ≪≫
    ShortComplex.homologyMapIso (scIso P R q) ≪≫
    (((R.mapHomologicalComplex _).obj P.cocomplex).homologyIsoSc' (q + 1) (q + 2) (q + 3) (by simp)
      (by simp only [CochainComplex.next]; rfl)).symm ≪≫
    (P.isoRightDerivedObj R (q + 2)).symm

end RamanujanPetersson.EtLeray

-- inlined from S4-EtLeray Low
namespace RamanujanPetersson.EtLeray


variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasInjectiveResolutions C] {N : C} (P : InjectiveResolution N) (R : C ⥤ D) [R.Additive]
  [PreservesFiniteLimits R]

/-- `R(P⁰) → R(P¹) → R(P²)`. -/
abbrev S01 : ShortComplex D := ((R.mapHomologicalComplex _).obj P.cocomplex).sc' 0 1 2

/-- `R(dQ) : R(Qc P) → R(P¹)`, typed into `S01`. -/
def RdQ : R.obj (Qc P) ⟶ (S01 P R).X₂ := R.map (dQ P)

theorem RdQ_g : RdQ P R ≫ (S01 P R).g = 0 := by
  change R.map (dQ P) ≫ R.map (P.cocomplex.d 1 2) = 0
  rw [← R.map_comp, dQ_d12, R.map_zero]

/-- `R(Qc P) ↪ R(P¹)` is a kernel of `R(P¹ → P²)`. -/
def RdQ_isKernel : IsLimit (KernelFork.ofι (RdQ P R) (RdQ_g P R)) :=
  KernelFork.mapIsLimit _ (shExact₀ P).fIsKernel R

/-- `Rπ : R P⁰ → R(Qc P)`. -/
abbrev Rπ : R.obj (P.cocomplex.X 0) ⟶ R.obj (Qc P) := R.map (cokernel.π (P.ι.f 0))

theorem lift_eq : (RdQ_isKernel P R).lift (KernelFork.ofι (S01 P R).f (S01 P R).zero) = Rπ P R := by
  apply Fork.IsLimit.hom_ext (RdQ_isKernel P R)
  refine ((RdQ_isKernel P R).fac _ WalkingParallelPair.zero).trans ?_
  change R.map (P.cocomplex.d 0 1) = R.map (cokernel.π (P.ι.f 0)) ≫ R.map (dQ P)
  rw [← R.map_comp, π_dQ]

/-- Left homology data of `R P⁰ → R P¹ → R P²` with cycles `R(Qc P)` and homology `coker(Rπ)`. -/
def h1Data : (S01 P R).LeftHomologyData where
  K := R.obj (Qc P)
  H := cokernel (Rπ P R)
  i := RdQ P R
  π := cokernel.π (Rπ P R)
  wi := RdQ_g P R
  hi := RdQ_isKernel P R
  wπ := (congrArg (fun g => g ≫ cokernel.π (Rπ P R)) (lift_eq P R)).trans (cokernel.condition _)
  hπ := CokernelCofork.isColimitOfIsColimitOfIff' (cokernelIsCokernel (Rπ P R)) _
    (fun _ φ => Iff.of_eq (congrArg (fun g => g ≫ φ = 0) (lift_eq P R).symm))

/-- **`R¹ N ≅ coker(R P⁰ → R(Qc P))`**. -/
def r1Iso : (R.rightDerived 1).obj N ≅ cokernel (Rπ P R) :=
  P.isoRightDerivedObj R 1 ≪≫
    ((R.mapHomologicalComplex _).obj P.cocomplex).homologyIsoSc' 0 1 2 (CochainComplex.prev_nat_succ 0)
      (CochainComplex.next ℕ 1) ≪≫ (h1Data P R).homologyIso

/-- `0 → im(Rπ) → R(Qc P) → coker(Rπ) → 0`. -/
abbrev baseSC : ShortComplex D :=
  ShortComplex.mk (Abelian.image.ι (Rπ P R)) (cokernel.π (Rπ P R)) (by
    rw [← cancel_epi (Abelian.factorThruImage (Rπ P R)), ← Category.assoc, Abelian.image.fac,
      cokernel.condition, comp_zero])

theorem baseSC_shortExact : (baseSC P R).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- `0 → R N → R P⁰ → im(Rπ) → 0`. -/
abbrev imSC : ShortComplex D :=
  ShortComplex.mk (R.map (P.ι.f 0)) (Abelian.factorThruImage (Rπ P R)) (by
    rw [← cancel_mono (Abelian.image.ι (Rπ P R)), Category.assoc, Abelian.image.fac, zero_comp,
      ← Functor.map_comp, cokernel.condition, Functor.map_zero])

theorem presQ_map_exact : ((presQ P).map R).Exact :=
  (presQ_shortExact P).exact.map_of_mono_of_preservesKernel R inferInstance inferInstance

theorem imSC_shortExact : (imSC P R).ShortExact where
  exact := by
    let φ : imSC P R ⟶ (presQ P).map R :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := Abelian.image.ι (Rπ P R)
        comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
        comm₂₃ := by
          change 𝟙 _ ≫ Rπ P R = Abelian.factorThruImage (Rπ P R) ≫ Abelian.image.ι (Rπ P R)
          rw [Abelian.image.fac, Category.id_comp] }
    have : Epi φ.τ₁ := (inferInstance : Epi (𝟙 (R.obj N)))
    have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 (R.obj (P.cocomplex.X 0))))
    have : Mono φ.τ₃ := (inferInstance : Mono (Abelian.image.ι (Rπ P R)))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (presQ_map_exact P R)
  mono_f := by
    change Mono (R.map (P.ι.f 0))
    infer_instance

/-- **`R¹ N = 0` ⇒ `R(N → P⁰ → Qc P)` is short exact.** -/
theorem presQ_map_shortExact (h1 : IsZero ((R.rightDerived 1).obj N)) : ((presQ P).map R).ShortExact where
  exact := presQ_map_exact P R
  mono_f := by
    change Mono (R.map (P.ι.f 0))
    infer_instance
  epi_g := by
    change Epi (Rπ P R)
    exact Preadditive.epi_of_isZero_cokernel _ (h1.of_iso (r1Iso P R).symm)

/-- `(imSC P R).X₁ = R N` is injective when `R N` is. -/
theorem injective_imSC_X₁ [Injective (R.obj N)] : Injective (imSC P R).X₁ := by
  change Injective (R.obj N); infer_instance

/-- `((presQ P).map R).X₁ = R N` is injective when `R N` is. -/
theorem injective_presQR_X₁ [Injective (R.obj N)] : Injective ((presQ P).map R).X₁ := by
  change Injective (R.obj N); infer_instance

variable [R.PreservesInjectiveObjects]

/-- `R N` injective ⇒ `im(Rπ)` injective. -/
theorem injective_im [Injective (R.obj N)] : Injective (Abelian.image (Rπ P R)) :=
  have := injective_imSC_X₁ P R
  Retract.injective { i := _, r := _, retract := ((imSC_shortExact P R).splittingOfInjective).s_g }

/-- `R N` injective and `R¹ N = 0` ⇒ `R(Qc P)` injective. -/
theorem injective_RQc [Injective (R.obj N)] (h1 : IsZero ((R.rightDerived 1).obj N)) :
    Injective (R.obj (Qc P)) := by
  have := injective_presQR_X₁ P R
  have : Injective ((presQ P).map R).X₂ :=
    Functor.PreservesInjectiveObjects.injective_obj (inferInstance : Injective (P.cocomplex.X 0))
  exact Retract.injective
    { i := _, r := _, retract := ((presQ_map_shortExact P R h1).splittingOfInjective).s_g }

end RamanujanPetersson.EtLeray

-- inlined from S4-EtLeray Acyc
namespace RamanujanPetersson.EtLeray


variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasExt.{w} C] [HasExt.{w} D]
variable {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] [R.Additive]
variable [EnoughInjectives C]

attribute [local instance] Ext.subsingleton_of_injective in
/-- **The edge map is bijective on `R`-acyclic objects.** -/
theorem edge_bijective (A : D) (n : ℕ) :
    ∀ (N : C), (∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj N)) →
      Function.Bijective (edge adj A N n) := by
  have : PreservesLimitsOfSize R := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits R := inferInstance
  have : L.PreservesMonomorphisms := inferInstance
  have hRI : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n with
  | zero => exact fun N _ => edge_zero_bijective adj A N
  | succ n ih =>
    intro N hN
    let P : InjectiveResolution N := injectiveResolution N
    let S := presQ P
    have hS : S.ShortExact := presQ_shortExact P
    have hRS : (S.map R).ShortExact := presQ_map_shortExact P R (hN 0)
    have hQ : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj (Qc P)) :=
      fun q => (hN (q + 1)).of_iso (dsIso P R q)
    have hP0 : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj (P.cocomplex.X 0)) :=
      fun q => R.isZero_rightDerived_obj_injective_succ q _
    have : Injective (S.map R).X₂ := Functor.PreservesInjectiveObjects.injective_obj
      (inferInstance : Injective (P.cocomplex.X 0))
    have : Injective S.X₂ := (inferInstance : Injective (P.cocomplex.X 0))
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (edge adj A S.X₂ n) (edge adj A S.X₃ n) (edge adj A S.X₁ (n + 1))
      (by ext x; exact (edge_comp_mk₀ adj A S.g x).symm)
      (by ext x; exact (edge_comp_extClass adj A hS hRS x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hRS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj A) hS n (n + 1) rfl))
      (ih _ hP0).surjective (ih _ hQ)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hRS y₁ (by subsingleton) rfl)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)

/-- **One-row Leray, row `0`**: `Ext^n(A, R N) ≃+ Ext^n(L A, N)` for `R`-acyclic `N`. -/
def edgeEquiv (A : D) (N : C) (hN : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj N)) (n : ℕ) :
    Ext A (R.obj N) n ≃+ Ext (L.obj A) N n :=
  AddEquiv.ofBijective (edge adj A N n) (edge_bijective adj A n N hN)

theorem edgeEquiv_apply (A : D) (N : C) (hN : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj N)) (n : ℕ)
    (x : Ext A (R.obj N) n) : edgeEquiv adj A N hN n x = edge adj A N n x :=
  rfl

end RamanujanPetersson.EtLeray

-- inlined from S4-EtLeray GS1
namespace RamanujanPetersson.EtLeray


section

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]

/-- Postcomposition with an isomorphism, as an additive equivalence. -/
def extIsoR (A : D) {X Y : D} (e : X ≅ Y) (n : ℕ) : Ext A X n ≃+ Ext A Y n where
  toFun x := x.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun y := y.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.comp_mk₀_id]
  right_inv y := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.comp_mk₀_id]
  map_add' x y := Ext.add_comp _ _ _ _

theorem extIsoR_apply (A : D) {X Y : D} (e : X ≅ Y) (n : ℕ) (x : Ext A X n) :
    extIsoR A e n x = x.comp (Ext.mk₀ e.hom) (add_zero n) :=
  rfl

end

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasExt.{w} C] [HasExt.{w} D]
variable {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] [R.Additive]
variable [PreservesFiniteLimits R] [EnoughInjectives C]
variable (A : D) {N : C} (P : InjectiveResolution N)

/-- `Φ : Ext^m(A, R(Qc P)) → Ext^(m+1)(L A, N)`, `x ↦ edge(x) ∘ δ`. -/
def phi1 (m : ℕ) : Ext A (R.obj (Qc P)) m →+ Ext (L.obj A) N (m + 1) :=
  ((presQ_shortExact P).extClass.postcomp (L.obj A) rfl).comp (edge adj A (Qc P) m)

theorem phi1_apply (m : ℕ) (x : Ext A (R.obj (Qc P)) m) :
    phi1 adj A P m x = (edge adj A (Qc P) m x).comp (presQ_shortExact P).extClass rfl :=
  rfl

/-- `β : Ext^m(A, R(Qc P)) → Ext^m(A, coker Rπ)`. -/
def beta1 (m : ℕ) : Ext A (R.obj (Qc P)) m →+ Ext A (cokernel (Rπ P R)) m :=
  (Ext.mk₀ (cokernel.π (Rπ P R))).postcomp A (add_zero m)

theorem beta1_apply (m : ℕ) (x : Ext A (R.obj (Qc P)) m) :
    beta1 A P m x = x.comp (Ext.mk₀ (cokernel.π (Rπ P R))) (add_zero m) :=
  rfl

variable (hN : ∀ q : ℕ, IsZero ((R.rightDerived (q + 2)).obj N))

include hN in
theorem qc_acyclic : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj (Qc P)) :=
  fun q => (hN q).of_iso (dsIso P R q)

attribute [local instance] Ext.subsingleton_of_injective

include hN in
theorem phi1_surjective (m : ℕ) : Function.Surjective (phi1 adj A P m) := by
  intro y
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (L.obj A) (presQ_shortExact P) y
    (by subsingleton) rfl
  obtain ⟨x, rfl⟩ := (edge_bijective adj A m (Qc P) (qc_acyclic P hN)).2 x₃
  exact ⟨x, hx₃⟩

include adj in
theorem beta1_surjective [Injective (R.obj N)] (m : ℕ) : Function.Surjective (beta1 A P (R := R) m) := by
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  have : Injective (Abelian.image (Rπ P R)) := injective_im P R
  intro z
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ A (baseSC_shortExact P R) z rfl (by subsingleton)
  exact ⟨x, hx⟩

include hN in
theorem ker_beta1_eq [Injective (R.obj N)] (m : ℕ) :
    (beta1 A P (R := R) m).ker = (phi1 adj A P m).ker := by
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  have hP0 : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj (P.cocomplex.X 0)) :=
    fun q => R.isZero_rightDerived_obj_injective_succ q _
  have := injective_imSC_X₁ P R
  ext x
  simp only [AddMonoidHom.mem_ker, beta1_apply, phi1_apply]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₂ A (baseSC_shortExact P R) x hx
    obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₃ A (imSC_shortExact P R) y rfl (by subsingleton)
    have e1 : (z.comp (Ext.mk₀ (Abelian.factorThruImage (Rπ P R))) (add_zero m)).comp
        (Ext.mk₀ (Abelian.image.ι (Rπ P R))) (add_zero m) = z.comp (Ext.mk₀ (R.map (cokernel.π (P.ι.f 0))))
          (add_zero m) := by
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Abelian.image.fac]
    change (edge adj A (Qc P) m ((z.comp (Ext.mk₀ (Abelian.factorThruImage (Rπ P R))) (add_zero m)).comp
        (Ext.mk₀ (Abelian.image.ι (Rπ P R))) (add_zero m))).comp (presQ_shortExact P).extClass rfl = 0
    rw [e1, edge_comp_mk₀, Ext.comp_assoc _ _ _ (add_zero m) (zero_add 1) (by omega),
      (presQ_shortExact P).comp_extClass, Ext.comp_zero]
  · intro hx
    obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ (L.obj A) (presQ_shortExact P) _ rfl hx
    obtain ⟨z, rfl⟩ := (edge_bijective adj A m _ hP0).2 w
    have hx' : x = z.comp (Ext.mk₀ (R.map (cokernel.π (P.ι.f 0)))) (add_zero m) := by
      apply (edge_bijective adj A m (Qc P) (qc_acyclic P hN)).1
      rw [edge_comp_mk₀]
      exact hw.symm
    rw [hx', Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    change z.comp (Ext.mk₀ (Rπ P R ≫ cokernel.π (Rπ P R))) (add_zero m) = 0
    rw [cokernel.condition, Ext.mk₀_zero, Ext.comp_zero]

include hN in
/-- `Ext^m(A, coker Rπ) ≃+ Ext^(m+1)(L A, N)`. -/
def row1Coker [Injective (R.obj N)] (m : ℕ) : Ext A (cokernel (Rπ P R)) m ≃+ Ext (L.obj A) N (m + 1) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _ (beta1_surjective adj A P m)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (ker_beta1_eq adj A P hN m)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (phi1_surjective adj A P hN m)))

include hN in
/-- **One-row Leray, row `1`**: `Ext^m(A, R¹ N) ≃+ Ext^(m+1)(L A, N)` when `R N` is injective and
`R^(q+2) N = 0` for all `q`. -/
def row1Equiv [Injective (R.obj N)] (m : ℕ) :
    Ext A ((R.rightDerived 1).obj N) m ≃+ Ext (L.obj A) N (m + 1) :=
  (extIsoR A (r1Iso P R) m).trans (row1Coker adj A P hN m)

end RamanujanPetersson.EtLeray

-- inlined from S4-EtLeray GSn
namespace RamanujanPetersson.EtLeray


section Delta

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

attribute [local instance] Ext.subsingleton_of_injective

/-- The connecting map `Ext^k(X, Qc P) → Ext^k'(X, N)` (`k + 1 = k'`). -/
def deltaQ (X : C) {N : C} (P : InjectiveResolution N) (k k' : ℕ) (h : k + 1 = k') :
    Ext X (Qc P) k →+ Ext X N k' :=
  (presQ_shortExact P).extClass.postcomp X h

theorem deltaQ_apply (X : C) {N : C} (P : InjectiveResolution N) (k k' : ℕ) (h : k + 1 = k')
    (x : Ext X (Qc P) k) : deltaQ X P k k' h x = x.comp (presQ_shortExact P).extClass h :=
  rfl

/-- In positive degrees the connecting map is bijective (`P⁰` is injective). -/
theorem deltaQ_bijective (X : C) {N : C} (P : InjectiveResolution N) (k k' : ℕ) (h : k + 1 + 1 = k') :
    Function.Bijective (deltaQ X P (k + 1) k' h) := by
  subst h
  have : Injective (presQ P).X₂ := (inferInstance : Injective (P.cocomplex.X 0))
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [deltaQ_apply] at hx
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ X (presQ_shortExact P) x rfl hx
    rw [Subsingleton.elim y 0, Ext.zero_comp]
  · intro y
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ X (presQ_shortExact P) y (by subsingleton) rfl
    exact ⟨x, hx⟩

/-- `Ext^(k+1)(X, Qc P) ≃+ Ext^k'(X, N)` for `k + 2 = k'`. -/
def deltaEquiv (X : C) {N : C} (P : InjectiveResolution N) (k k' : ℕ) (h : k + 1 + 1 = k') :
    Ext X (Qc P) (k + 1) ≃+ Ext X N k' :=
  AddEquiv.ofBijective (deltaQ X P (k + 1) k' h) (deltaQ_bijective X P k k' h)

end Delta

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasExt.{w} C] [HasExt.{w} D]
variable {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] [R.Additive]
variable [PreservesFiniteLimits R] [EnoughInjectives C]
variable (A : D)

/-- Rows `j + 1 ≥ 1`: `R N` injective, `R^(q+1) N = 0` for `q ≠ j` ⇒
`Ext^m(A, R^(j+1) N) ≃+ Ext^(m+(j+1))(L A, N)`. -/
def rowEquiv : (j : ℕ) → (N : C) → Injective (R.obj N) →
    (∀ q : ℕ, q ≠ j → IsZero ((R.rightDerived (q + 1)).obj N)) → (m : ℕ) →
    Ext A ((R.rightDerived (j + 1)).obj N) m ≃+ Ext (L.obj A) N (m + (j + 1))
  | 0, N, hI, hN, m =>
    haveI : Injective (R.obj N) := hI
    row1Equiv adj A (injectiveResolution N) (fun q => hN (q + 1) (by omega)) m
  | j + 1, N, hI, hN, m =>
    haveI : Injective (R.obj N) := hI
    haveI : R.PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
    (extIsoR A (dsIso (injectiveResolution N) R j).symm m).trans
      ((rowEquiv j (Qc (injectiveResolution N))
        (injective_RQc (injectiveResolution N) R (hN 0 (by omega)))
        (fun q hq => (hN (q + 1) (by omega)).of_iso (dsIso (injectiveResolution N) R q)) m).trans
        (deltaEquiv (L.obj A) (injectiveResolution N) (m + j) (m + (j + 1 + 1)) (by omega)))

/-- **One-row Leray**: if `R^q N = 0` for all `q ≠ i`, then `Ext^m(A, R^i N) ≃+ Ext^(m+i)(L A, N)`. -/
def lerayRowEquiv : (i : ℕ) → (N : C) → (∀ q : ℕ, q ≠ i → IsZero ((R.rightDerived q).obj N)) → (m : ℕ) →
    Ext A ((R.rightDerived i).obj N) m ≃+ Ext (L.obj A) N (m + i)
  | 0, N, hN, m =>
    (extIsoR A (R.rightDerivedZeroIsoSelf.app N) m).trans
      (edgeEquiv adj A N (fun q => hN (q + 1) (by omega)) m)
  | j + 1, N, hN, m =>
    rowEquiv adj A j N
      ((hN 0 (by omega)).of_iso (R.rightDerivedZeroIsoSelf.app N).symm).injective
      (fun q hq => hN (q + 1) (by omega)) m

end RamanujanPetersson.EtLeray

end

theorem solution
    {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasExt.{w} C] [HasExt.{w} D] [EnoughInjectives C]
    {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.Additive] [PreservesFiniteLimits R]
    (A : D) (N : C) (i : ℕ) (hN : ∀ q : ℕ, q ≠ i → IsZero ((R.rightDerived q).obj N)) (m : ℕ) :
    Nonempty (Ext A ((R.rightDerived i).obj N) m ≃+ Ext (L.obj A) N (m + i)) := by
  exact ⟨RamanujanPetersson.EtLeray.lerayRowEquiv adj A i N hN m⟩
