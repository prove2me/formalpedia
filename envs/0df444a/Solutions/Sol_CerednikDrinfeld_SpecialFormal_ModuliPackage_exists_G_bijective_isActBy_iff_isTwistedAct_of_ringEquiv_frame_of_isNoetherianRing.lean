-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/75790c53-ad9a-5fdd-8627-77d7f29e6d97

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct

namespace R4F4b

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvPowerSeries

universe u

variable {p : ℕ} [Fact p.Prime]

theorem invertible_of_semilinearEquiv {R S : Type*} [CommRing R] [CommRing S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : M ≃ₛₗ[σ] N) [Module.Invertible R M] : Module.Invertible S N := by
  letI : Algebra R S := σ.toAlgebra
  letI instRN : Module R N := Module.compHom N σ
  haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r n => rfl
  let eR : M →ₗ[R] N :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun r m => e.map_smulₛₗ r m }
  let ε₀ : S ⊗[R] M →ₗ[S] N :=
    TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : S →ₗ[S] S).smulRight eR)
  have hε₀ : ∀ (s : S) (m : M), ε₀ (s ⊗ₜ m) = s • e m := fun s m => rfl
  let g : N → S ⊗[R] M := fun n => (1 : S) ⊗ₜ e.symm n
  have hσ : ∀ s : S, σ (σ' s) = s := fun s => RingHomInvPair.comp_apply_eq₂
  have hg : Function.LeftInverse g ε₀ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [g]
    | tmul s m =>
      simp only [g, hε₀, LinearEquiv.map_smulₛₗ e.symm, LinearEquiv.symm_apply_apply]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      show σ (σ' s) ⊗ₜ[R] m = s ⊗ₜ[R] m
      rw [hσ]
    | add x y hx hy =>
      simp only [g, map_add, TensorProduct.tmul_add] at hx hy ⊢
      rw [hx, hy]
  have hg' : Function.RightInverse g ε₀ := by
    intro n
    simp only [g, hε₀, one_smul, LinearEquiv.apply_symm_apply]
  exact Module.Invertible.congr (LinearEquiv.ofBijective ε₀ ⟨hg.injective, hg'.surjective⟩)

noncomputable def mvPowerSeriesMapEquiv {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B') :
    MvPowerSeries (Fin 2) B ≃+* MvPowerSeries (Fin 2) B' :=
  RingEquiv.ofRingHom (MvPowerSeries.map (f : B →+* B')) (MvPowerSeries.map (f.symm : B' →+* B))
    (by rw [← MvPowerSeries.map_comp]; convert MvPowerSeries.map_id; ext x; simp)
    (by rw [← MvPowerSeries.map_comp]; convert MvPowerSeries.map_id; ext x; simp)

theorem mvPowerSeriesMapEquiv_apply {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B')
    (x : MvPowerSeries (Fin 2) B) : mvPowerSeriesMapEquiv f x = MvPowerSeries.map (f : B →+* B') x := rfl

theorem span_range_map {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B') (φ : Series B) :
    Ideal.span (Set.range (φ.map (f : B →+* B'))) =
      (Ideal.span (Set.range φ)).map (mvPowerSeriesMapEquiv f : MvPowerSeries (Fin 2) B →+* _) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem hasKernelOfDegree_map_ringEquiv {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B')
    (φ : Series B) (d : ℕ) (h : FormalODModule.HasKernelOfDegree φ d) :
    FormalODModule.HasKernelOfDegree (φ.map (f : B →+* B')) d := by
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.of_ringEquiv_symm f
  obtain ⟨hfin, hproj, hrk⟩ := h

  let θR : FormalODModule.KerAlgebra φ ≃+* FormalODModule.KerAlgebra (φ.map (f : B →+* B')) :=
    Ideal.quotientEquiv _ _ (mvPowerSeriesMapEquiv f) (span_range_map f φ)
  have hθmk : ∀ y, θR (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (MvPowerSeries.map (f : B →+* B') y) :=
    fun y => rfl
  have hsm : ∀ (b : B) (y : MvPowerSeries (Fin 2) B),
      b • (Ideal.Quotient.mk (Ideal.span (Set.range φ)) y : FormalODModule.KerAlgebra φ) =
        Ideal.Quotient.mk _ (C b * y) := by
    intro b y; rw [← smul_eq_C_mul]; rfl
  have hsm' : ∀ (b : B') (y : MvPowerSeries (Fin 2) B'),
      b • (Ideal.Quotient.mk (Ideal.span (Set.range (φ.map (f : B →+* B')))) y :
        FormalODModule.KerAlgebra (φ.map (f : B →+* B'))) = Ideal.Quotient.mk _ (C b * y) := by
    intro b y; rw [← smul_eq_C_mul]; rfl
  let θ : FormalODModule.KerAlgebra φ ≃ₛₗ[(f : B →+* B')] FormalODModule.KerAlgebra (φ.map (f : B →+* B')) :=
    { toFun := θR
      map_add' := θR.map_add
      map_smul' := fun b x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        show θR (b • Ideal.Quotient.mk _ y) = (f : B →+* B') b • θR (Ideal.Quotient.mk _ y)
        rw [hsm, hθmk, hθmk, map_mul, MvPowerSeries.map_C, RingEquiv.coe_toRingHom, hsm']
      invFun := θR.symm
      left_inv := θR.left_inv
      right_inv := θR.right_inv }
  refine ⟨Module.Finite.of_surjective θ.toLinearMap θ.surjective, Module.Projective.of_equiv θ, fun κ _ g => ?_⟩
  rw [Series.map_map]
  exact hrk κ (g.comp (f : B →+* B'))

theorem hasKernelOfDegree_map_ringEquiv_iff {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B')
    (φ : Series B) (d : ℕ) :
    FormalODModule.HasKernelOfDegree (φ.map (f : B →+* B')) d ↔ FormalODModule.HasKernelOfDegree φ d := by
  refine ⟨fun h => ?_, hasKernelOfDegree_map_ringEquiv f φ d⟩
  have h' := hasKernelOfDegree_map_ringEquiv f.symm _ d h
  rw [Series.map_map] at h'
  convert h'
  rw [eq_comm]
  convert Series.map_ringHom_id φ
  ext x
  simp

noncomputable def endMap {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') (F : MvFormalGroup 2 B) [F.IsComm]
    [(F.map f).IsComm] : MvFormalGroup.End F →+* MvFormalGroup.End (F.map f) where
  toFun e := ((IsLawHom.of_hom e).map f).toHom
  map_one' := by
    apply MvFormalGroup.Hom.ext
    show (Series.id B).map f = _
    rw [Series.map_id]; rfl
  map_mul' e e' := by
    apply MvFormalGroup.Hom.ext
    show Series.map f (Series.comp (MvFormalGroup.Hom.toPowerSeries e) (MvFormalGroup.Hom.toPowerSeries e')) =
      Series.comp (Series.map f (MvFormalGroup.Hom.toPowerSeries e)) (Series.map f (MvFormalGroup.Hom.toPowerSeries e'))
    exact Series.map_comp f _ _ (MvFormalGroup.Hom.constantCoeff_eq_zero e')
  map_zero' := by
    apply MvFormalGroup.Hom.ext
    funext i
    show MvPowerSeries.map f ((0 : MvFormalGroup.End F).toPowerSeries i) = (0 : MvFormalGroup.End (F.map f)).toPowerSeries i
    rw [MvFormalGroup.End.toPowerSeries_zero, MvFormalGroup.End.toPowerSeries_zero, map_zero]
  map_add' e e' := by
    apply MvFormalGroup.Hom.ext
    show Series.map f (Series.addVia F (MvFormalGroup.Hom.toPowerSeries e) (MvFormalGroup.Hom.toPowerSeries e')) =
      Series.addVia (F.map f) (Series.map f (MvFormalGroup.Hom.toPowerSeries e)) (Series.map f (MvFormalGroup.Hom.toPowerSeries e'))
    exact Series.map_addVia f F _ _ (MvFormalGroup.Hom.constantCoeff_eq_zero e) (MvFormalGroup.Hom.constantCoeff_eq_zero e')

@[scoped simp] theorem endMap_toPowerSeries {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') (F : MvFormalGroup 2 B)
    [F.IsComm] [(F.map f).IsComm] (e : MvFormalGroup.End F) :
    MvFormalGroup.Hom.toPowerSeries (endMap f F e) = Series.map f (MvFormalGroup.Hom.toPowerSeries e) := rfl

theorem endMap_bijective {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B') (F : MvFormalGroup 2 B)
    [F.IsComm] [(F.map (f : B →+* B')).IsComm] : Function.Bijective (endMap (f : B →+* B') F) := by
  have hback : (F.map (f : B →+* B')).map (f.symm : B' →+* B) = F := by
    rw [MvFormalGroup.map_map']
    convert MvFormalGroup.map_ringHom_id F
    ext x; simp
  have hround : ∀ s : Series B, Series.map (f.symm : B' →+* B) (Series.map (f : B →+* B') s) = s := by
    intro s
    rw [Series.map_map]
    convert Series.map_ringHom_id s
    ext x; simp
  have hround' : ∀ s : Series B', Series.map (f : B →+* B') (Series.map (f.symm : B' →+* B) s) = s := by
    intro s
    rw [Series.map_map]
    convert Series.map_ringHom_id s
    ext x; simp
  constructor
  · intro e e' h
    apply MvFormalGroup.Hom.ext
    have h2 := congrArg MvFormalGroup.Hom.toPowerSeries h
    rw [endMap_toPowerSeries, endMap_toPowerSeries] at h2
    rw [← hround (MvFormalGroup.Hom.toPowerSeries e), h2, hround]
  · intro e'
    have hlaw : IsLawHom F F (Series.map (f.symm : B' →+* B) (MvFormalGroup.Hom.toPowerSeries e')) := by
      have := (IsLawHom.of_hom e').map (f.symm : B' →+* B)
      rwa [hback] at this
    refine ⟨hlaw.toHom, MvFormalGroup.Hom.ext ?_⟩
    rw [endMap_toPowerSeries]
    exact hround' _

noncomputable def endEquiv {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B') (F : MvFormalGroup 2 B)
    [F.IsComm] [(F.map (f : B →+* B')).IsComm] : MvFormalGroup.End F ≃+* MvFormalGroup.End (F.map (f : B →+* B')) :=
  RingEquiv.ofBijective (endMap (f : B →+* B') F) (endMap_bijective f F)

theorem endEquiv_toPowerSeries {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B') (F : MvFormalGroup 2 B)
    [F.IsComm] [(F.map (f : B →+* B')).IsComm] (e : MvFormalGroup.End F) :
    MvFormalGroup.Hom.toPowerSeries (endEquiv f F e) = Series.map (f : B →+* B') (MvFormalGroup.Hom.toPowerSeries e) := rfl

theorem linearPart_map {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') (φ : Series B) :
    MvFormalGroup.linearPart (φ.map f) = (MvFormalGroup.linearPart φ).map f := by
  ext i j
  rfl

theorem lieAct_map_apply {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') (X : FormalODModule p B)
    (a : Zp2 p) (v : Fin 2 → B) :
    (X.map f).lieAct a (f ∘ v) = f ∘ (X.lieAct a v) := by
  funext i
  show ((MvFormalGroup.linearPart ((X.act a).map f)).mulVec (f ∘ v)) i = f ((MvFormalGroup.linearPart (X.act a)).mulVec v i)
  rw [linearPart_map, RingHom.map_mulVec]

theorem mem_lieZero_iff {B : Type u} [CommRing B] (j : Zp2 p →+* B) (X : FormalODModule p B) (v : Fin 2 → B) :
    v ∈ X.lieZero j ↔ ∀ a, X.lieAct a v = j a • v := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_lieOne_iff {B : Type u} [CommRing B] (j : Zp2 p →+* B) (X : FormalODModule p B) (v : Fin 2 → B) :
    v ∈ X.lieOne j ↔ ∀ a, X.lieAct a v = j (WittVector.frobenius a) • v := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem isSpecial_map_ringEquiv {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B')
    (j : Zp2 p →+* B) (X : FormalODModule p B) (h : X.IsSpecial j) :
    (X.map (f : B →+* B')).IsSpecial ((f : B →+* B').comp j) := by
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.of_ringEquiv_symm f
  obtain ⟨hc, h0, h1⟩ := h

  let θ : (Fin 2 → B) ≃ₛₗ[(f : B →+* B')] (Fin 2 → B') :=
    { toFun := fun v => f ∘ v
      map_add' := fun v w => by funext i; exact f.map_add (v i) (w i)
      map_smul' := fun b v => by funext i; exact f.map_mul b (v i)
      invFun := fun v => f.symm ∘ v
      left_inv := fun v => by funext i; exact f.symm_apply_apply (v i)
      right_inv := fun v => by funext i; exact f.apply_symm_apply (v i) }
  have hθ : ∀ v, θ v = ((f : B →+* B') : B → B') ∘ v := fun v => rfl
  have key0 : (X.map (f : B →+* B')).lieZero ((f : B →+* B').comp j) = (X.lieZero j).map θ.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_lieZero_iff, mem_lieZero_iff]
    have hv : v = θ (θ.symm v) := (θ.apply_symm_apply v).symm
    constructor
    · intro H a
      have H' := H a
      rw [hv, hθ, lieAct_map_apply] at H'
      funext i
      apply f.injective
      have := congrFun H' i
      simpa [Pi.smul_apply, smul_eq_mul, map_mul] using this
    · intro H a
      rw [hv, hθ, lieAct_map_apply, H a]
      funext i
      simp [Pi.smul_apply, smul_eq_mul, map_mul]
  have key1 : (X.map (f : B →+* B')).lieOne ((f : B →+* B').comp j) = (X.lieOne j).map θ.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_lieOne_iff, mem_lieOne_iff]
    have hv : v = θ (θ.symm v) := (θ.apply_symm_apply v).symm
    constructor
    · intro H a
      have H' := H a
      rw [hv, hθ, lieAct_map_apply] at H'
      funext i
      apply f.injective
      have := congrFun H' i
      simpa [Pi.smul_apply, smul_eq_mul, map_mul] using this
    · intro H a
      rw [hv, hθ, lieAct_map_apply, H a]
      funext i
      simp [Pi.smul_apply, smul_eq_mul, map_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [key0, key1]
    exact (Submodule.orderIsoMapComap θ).isCompl hc
  · rw [key0]
    haveI := h0
    exact invertible_of_semilinearEquiv (θ.submoduleMap (X.lieZero j))
  · rw [key1]
    haveI := h1
    exact invertible_of_semilinearEquiv (θ.submoduleMap (X.lieOne j))

theorem hasHeight_map_ringEquiv {B B' : Type u} [CommRing B] [CommRing B'] (f : B ≃+* B')
    (X : FormalODModule p B) (n : ℕ) (h : X.HasHeight n) : (X.map (f : B →+* B')).HasHeight n :=
  hasKernelOfDegree_map_ringEquiv f _ _ h

section Frame

variable {r : ℕ} [Fact r.Prime]
variable {Onr : Type} [CommRing Onr] {Onr' : Type} [CommRing Onr'] (eO : Onr ≃+* Onr')

theorem residueMap_comp_residueMap :
    (residueMap (p := r) (eO.symm : Onr' →+* Onr)).comp (residueMap (p := r) (eO : Onr →+* Onr')) = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun x => by simp [residueMap])

noncomputable def qbar : Onr ⧸ pIdeal r Onr ≃+* Onr' ⧸ pIdeal r Onr' :=
  RingEquiv.ofRingHom (residueMap (p := r) (eO : Onr →+* Onr')) (residueMap (p := r) (eO.symm : Onr' →+* Onr))
    (by simpa using residueMap_comp_residueMap (r := r) eO.symm) (residueMap_comp_residueMap eO)

theorem coe_qbar : ((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* Onr' ⧸ pIdeal r Onr') : Onr ⧸ pIdeal r Onr →+* Onr' ⧸ pIdeal r Onr') =
    residueMap (p := r) (eO : Onr →+* Onr') :=
  RingHom.ext fun _ => rfl

theorem residueMap_comp_eO {L : Type} [CommRing L] (χ : Onr' →+* L) :
    residueMap (p := r) (χ.comp (eO : Onr →+* Onr')) =
      (residueMap (p := r) χ).comp ((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* _) : Onr ⧸ pIdeal r Onr →+* Onr' ⧸ pIdeal r Onr') :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl)

variable (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))

def iota' : Zp2 r →+* Onr' := (eO : Onr →+* Onr').comp ι

noncomputable def Phi' : FormalODModule r (Onr' ⧸ pIdeal r Onr') :=
  Φ.map ((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* _) : Onr ⧸ pIdeal r Onr →+* Onr' ⧸ pIdeal r Onr')

theorem mk_comp_iota' :
    (Ideal.Quotient.mk (pIdeal r Onr')).comp (iota' eO ι) =
      (((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* _) : Onr ⧸ pIdeal r Onr →+* Onr' ⧸ pIdeal r Onr')).comp
        ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι) :=
  RingHom.ext fun _ => rfl

variable (M : ModuliPackage.{0, 0} r Onr)

def M' : ModuliPackage.{0, 0} r Onr' where
  obj B _ ψ hB := M.obj B (ψ.comp (eO : Onr →+* Onr')) hB
  map hB hB' f hf := M.map hB hB' f (by rw [← RingHom.comp_assoc, hf])
  map_id hB x := M.map_id hB x
  map_comp hB hB' hB'' g f hf hg x := M.map_comp hB hB' hB'' g f _ _ x

theorem isZariskiSheaf_M' (hM : M.IsZariskiSheaf) : (M' eO M).IsZariskiSheaf :=
  fun B _ ψ hB n f hf L _ _ _ hL L₂ _ _ _ hL₂ l rr hl hr =>
    hM B (ψ.comp (eO : Onr →+* Onr')) hB n f hf L hL L₂ hL₂ l rr hl hr

variable {Φ} in

def toSrc {B : Type} [CommRing B] (t : Rigidified r (Phi' eO Φ) B) : Rigidified r Φ B := ⟨t.X, t.n, t.ρ⟩

variable {Φ} in

def ofSrc {B : Type} [CommRing B] (t : Rigidified r Φ B) : Rigidified r (Phi' eO Φ) B := ⟨t.X, t.n, t.ρ⟩

variable {Φ} in
@[scoped simp] theorem toSrc_ofSrc {B : Type} [CommRing B] (t : Rigidified r Φ B) : toSrc eO (ofSrc eO t) = t := rfl
variable {Φ} in
@[scoped simp] theorem ofSrc_toSrc {B : Type} [CommRing B] (t : Rigidified r (Phi' eO Φ) B) : ofSrc eO (toSrc eO t) = t := rfl

variable {Φ} in
theorem toSrc_map {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B') (t : Rigidified r (Phi' eO Φ) B) :
    toSrc eO (t.map f) = (toSrc eO t).map f := rfl

variable {Φ} in
theorem Φbar_eq {B : Type} [CommRing B] (ψ : Onr' →+* B) (t : Rigidified r (Phi' eO Φ) B) :
    t.Φbar ψ = (toSrc eO t).Φbar (ψ.comp (eO : Onr →+* Onr')) := by
  show (Φ.map _).map (residueMap ψ) = Φ.map (residueMap (ψ.comp (eO : Onr →+* Onr')))
  rw [FormalODModule.map_map, residueMap_comp_eO]

variable {Φ} in
theorem isAdmissible_iff {B : Type} [CommRing B] (ψ : Onr' →+* B) (t : Rigidified r (Phi' eO Φ) B) :
    t.IsAdmissible (iota' eO ι) ψ ↔ (toSrc eO t).IsAdmissible ι (ψ.comp (eO : Onr →+* Onr')) := by
  unfold Rigidified.IsAdmissible
  rw [Φbar_eq]
  rfl

variable {Φ} in
theorem isIsomorphic_iff {B : Type} [CommRing B] (t t' : Rigidified r (Phi' eO Φ) B) :
    t.IsIsomorphic t' ↔ (toSrc eO t).IsIsomorphic (toSrc eO t') := Iff.rfl

variable {Φ} in
theorem rigidified_isTranslate_iff {B : Type} [CommRing B] (χ : Onr' →+* B) (ε : Series (Onr ⧸ pIdeal r Onr)) (k m' : ℕ)
    (t t' : Rigidified r (Phi' eO Φ) B) :
    Rigidified.IsTranslate (ε.map ((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* _) : _ →+* Onr' ⧸ pIdeal r Onr')) k m' χ t t' ↔
      Rigidified.IsTranslate ε k m' (χ.comp (eO : Onr →+* Onr')) (toSrc eO t) (toSrc eO t') := by
  unfold Rigidified.IsTranslate
  rw [Series.map_map, ← residueMap_comp_eO]
  rfl

variable {Φ} in
theorem rigidified_isPiTranslate_iff {B : Type} [CommRing B] (χ : Onr' →+* B) (t t' : Rigidified r (Phi' eO Φ) B) :
    Rigidified.IsPiTranslate χ t t' ↔ Rigidified.IsPiTranslate (χ.comp (eO : Onr →+* Onr')) (toSrc eO t) (toSrc eO t') := by
  unfold Rigidified.IsPiTranslate
  have : (Phi' eO Φ).varpi.map (residueMap χ) = Φ.varpi.map (residueMap (χ.comp (eO : Onr →+* Onr'))) := by
    show (Φ.varpi.map _).map (residueMap χ) = _
    rw [Series.map_map, ← residueMap_comp_eO]
  rw [this]
  rfl

variable {M} {Φ}
variable (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)

def eta' (B : Type) [CommRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)) (t : Rigidified r (Phi' eO Φ) B) :
    (M' eO M).obj B ψ hB :=
  η B (ψ.comp (eO : Onr →+* Onr')) hB (toSrc eO t)

theorem eta'_law1 {B : Type} [CommRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B))
    (h1 : ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι (ψ.comp (eO : Onr →+* Onr')) →
      t'.IsAdmissible ι (ψ.comp (eO : Onr →+* Onr')) →
      (η B (ψ.comp (eO : Onr →+* Onr')) hB t = η B (ψ.comp (eO : Onr →+* Onr')) hB t' ↔ t.IsIsomorphic t'))
    (t t' : Rigidified r (Phi' eO Φ) B) (ht : t.IsAdmissible (iota' eO ι) ψ) (ht' : t'.IsAdmissible (iota' eO ι) ψ) :
    (eta' eO η B ψ hB t = eta' eO η B ψ hB t' ↔ t.IsIsomorphic t') := by
  rw [isIsomorphic_iff]
  exact h1 _ _ ((isAdmissible_iff eO ι ψ t).1 ht) ((isAdmissible_iff eO ι ψ t').1 ht')

theorem eta'_law2 {B B' : Type} [CommRing B] [CommRing B'] (ψ : Onr' →+* B) (ψ' : Onr' →+* B')
    (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B') (hf : f.comp ψ = ψ')
    (h2 : ∀ (hf₀ : f.comp (ψ.comp (eO : Onr →+* Onr')) = ψ'.comp (eO : Onr →+* Onr')) (t : Rigidified r Φ B),
      t.IsAdmissible ι (ψ.comp (eO : Onr →+* Onr')) →
      η B' (ψ'.comp (eO : Onr →+* Onr')) hB' (t.map f) = M.map hB hB' f hf₀ (η B (ψ.comp (eO : Onr →+* Onr')) hB t))
    (t : Rigidified r (Phi' eO Φ) B) (ht : t.IsAdmissible (iota' eO ι) ψ) :
    eta' eO η B' ψ' hB' (t.map f) = (M' eO M).map hB hB' f hf (eta' eO η B ψ hB t) :=
  h2 (by rw [← RingHom.comp_assoc, hf]) _ ((isAdmissible_iff eO ι ψ t).1 ht)

theorem eta'_law3 {B : Type} [CommRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)) (m : (M' eO M).obj B ψ hB)
    (h3 : ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L] (hL : IsNilpotent (r : L)),
        ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp (ψ.comp (eO : Onr →+* Onr'))) ∧
          η L ((algebraMap B L).comp (ψ.comp (eO : Onr →+* Onr'))) hL t =
            M.map (ψ' := (algebraMap B L).comp (ψ.comp (eO : Onr →+* Onr'))) hB hL (algebraMap B L) rfl m) :
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L] (hL : IsNilpotent (r : L)),
        ∃ t : Rigidified r (Phi' eO Φ) L, t.IsAdmissible (iota' eO ι) ((algebraMap B L).comp ψ) ∧
          eta' eO η L ((algebraMap B L).comp ψ) hL t =
            (M' eO M).map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m := by
  obtain ⟨n, f, hf, H⟩ := h3
  refine ⟨n, f, hf, fun i L _ _ _ hL => ?_⟩
  obtain ⟨t, ht, hη⟩ := H i L hL
  exact ⟨ofSrc eO t, (isAdmissible_iff eO ι _ _).2 ht, hη⟩

theorem eta'_law3N {B : Type} [CommRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)) (m : (M' eO M).obj B ψ hB)
    (h3 : ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L] (hL : IsNilpotent (r : L)),
        ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp (ψ.comp (eO : Onr →+* Onr'))) ∧
          η L ((algebraMap B L).comp (ψ.comp (eO : Onr →+* Onr'))) hL t =
            M.map (ψ' := (algebraMap B L).comp (ψ.comp (eO : Onr →+* Onr'))) hB hL (algebraMap B L) rfl m) :
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L] (hL : IsNilpotent (r : L)),
        ∃ t : Rigidified r (Phi' eO Φ) L, t.IsAdmissible (iota' eO ι) ((algebraMap B L).comp ψ) ∧
          eta' eO η L ((algebraMap B L).comp ψ) hL t =
            (M' eO M).map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m := by
  obtain ⟨n, f, hf, H⟩ := h3
  refine ⟨n, f, hf, fun i L _ _ _ _ hL => ?_⟩
  obtain ⟨t, ht, hη⟩ := H i L hL
  exact ⟨ofSrc eO t, (isAdmissible_iff eO ι _ _).2 ht, hη⟩

variable (Φ)

def cEnd : MvFormalGroup.End Φ.F ≃+* MvFormalGroup.End (Phi' eO Φ).F :=
  @endEquiv _ _ _ _ (qbar (r := r) eO) Φ.F Φ.isComm (Phi' eO Φ).isComm

theorem cEnd_toPowerSeries (x : MvFormalGroup.End Φ.F) :
    MvFormalGroup.Hom.toPowerSeries (cEnd eO Φ x) =
      Series.map ((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* _) : _ →+* Onr' ⧸ pIdeal r Onr') (MvFormalGroup.Hom.toPowerSeries x) :=
  rfl

theorem cEnd_actEnd (a : Zp2 r) : cEnd eO Φ (Φ.actEnd a) = (Phi' eO Φ).actEnd a := MvFormalGroup.Hom.ext rfl

theorem cEnd_varpiEnd : cEnd eO Φ Φ.varpiEnd = (Phi' eO Φ).varpiEnd := MvFormalGroup.Hom.ext rfl

theorem image_cEnd :
    (cEnd eO Φ) '' (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) = Set.range (Phi' eO Φ).actEnd ∪ {(Phi' eO Φ).varpiEnd} := by
  rw [Set.image_union, Set.image_singleton, cEnd_varpiEnd, ← Set.range_comp,
    show ((cEnd eO Φ) ∘ Φ.actEnd) = (Phi' eO Φ).actEnd from funext fun a => cEnd_actEnd eO Φ a]

theorem map_centralizer :
    (Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})).map (cEnd eO Φ).toRingHom =
      Subring.centralizer (Set.range (Phi' eO Φ).actEnd ∪ {(Phi' eO Φ).varpiEnd}) := by
  rw [← image_cEnd]
  ext y
  rw [Subring.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subring.mem_centralizer_iff] at hx
    rw [Subring.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    show cEnd eO Φ g * cEnd eO Φ x = cEnd eO Φ x * cEnd eO Φ g
    rw [← map_mul, ← map_mul, hx g hg]
  · intro hy
    refine ⟨(cEnd eO Φ).symm y, ?_, (cEnd eO Φ).apply_symm_apply y⟩
    rw [Subring.mem_centralizer_iff]
    intro g hg
    apply (cEnd eO Φ).injective
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply]
    exact (Subring.mem_centralizer_iff.mp hy) _ ⟨g, hg, rfl⟩

def cCent : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) ≃+*
    Subring.centralizer (Set.range (Phi' eO Φ).actEnd ∪ {(Phi' eO Φ).varpiEnd}) :=
  (RingEquiv.subringMap (s := Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (cEnd eO Φ)).trans
    (RingEquiv.subringCongr (map_centralizer eO Φ))

theorem coe_cCent (x : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) :
    ((cCent eO Φ x : Subring.centralizer _) : MvFormalGroup.End (Phi' eO Φ).F) = cEnd eO Φ x := rfl

variable {K₀ : Type} [Field K₀] {K₀' : Type} [Field K₀'] (eK : K₀ ≃+* K₀')
variable (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)

def E0' : Subring.centralizer (Set.range (Phi' eO Φ).actEnd ∪ {(Phi' eO Φ).varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀' :=
  (eK : K₀ ≃+* K₀').toRingHom.mapMatrix.comp (E₀.comp (cCent eO Φ).symm.toRingHom)

theorem E0'_apply (x : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) :
    E0' eO Φ eK E₀ (cCent eO Φ x) = (E₀ x).map eK := by
  simp [E0']

theorem E0'_apply' (y : Subring.centralizer (Set.range (Phi' eO Φ).actEnd ∪ {(Phi' eO Φ).varpiEnd})) :
    E0' eO Φ eK E₀ y = (E₀ ((cCent eO Φ).symm y)).map eK := by
  simp [E0']

theorem E0'_injective (hE : Function.Injective E₀) : Function.Injective (E0' eO Φ eK E₀) := by
  intro y y' h
  rw [E0'_apply', E0'_apply'] at h
  exact (cCent eO Φ).symm.injective (hE (Matrix.map_injective eK.injective h))

theorem map_smul_natCast_pow (m : ℕ) (A : Matrix (Fin 2) (Fin 2) K₀) :
    ((r : K₀) ^ m • A).map eK = (r : K₀') ^ m • A.map eK := by
  ext i j
  simp [Matrix.map_apply, map_pow, map_natCast]

theorem E0'_comm {𝒪 : Type} [CommRing 𝒪] [Algebra 𝒪 K₀] {𝒪' : Type} [CommRing 𝒪'] [Algebra 𝒪' K₀'] (eb : 𝒪 ≃+* 𝒪')
    (hcomm : ∀ x : 𝒪, eK (algebraMap 𝒪 K₀ x) = algebraMap 𝒪' K₀' (eb x))
    (m : ℕ) (h₁ : ∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀))
    (h₂ : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)) :
    (∀ A : Matrix (Fin 2) (Fin 2) 𝒪', ∃ e, E0' eO Φ eK E₀ e = (r : K₀') ^ m • A.map (algebraMap 𝒪' K₀')) ∧
    (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪', (r : K₀') ^ m • E0' eO Φ eK E₀ e = A.map (algebraMap 𝒪' K₀')) := by
  have hmap : ∀ A : Matrix (Fin 2) (Fin 2) 𝒪, (A.map (algebraMap 𝒪 K₀)).map eK = (A.map eb).map (algebraMap 𝒪' K₀') := by
    intro A; ext i j; simp [Matrix.map_apply, hcomm]
  constructor
  · intro A'
    obtain ⟨e, he⟩ := h₁ (A'.map eb.symm)
    refine ⟨cCent eO Φ e, ?_⟩
    have hA' : (A'.map eb.symm).map eb = A' := by ext i j; simp
    rw [E0'_apply, he, map_smul_natCast_pow, hmap, hA']
  · intro y
    obtain ⟨A, hA⟩ := h₂ ((cCent eO Φ).symm y)
    refine ⟨A.map eb, ?_⟩
    rw [E0'_apply', ← map_smul_natCast_pow, hA, hmap]

variable {Φ}
variable {𝒪 : Type} [CommRing 𝒪] {𝒪' : Type} [CommRing 𝒪'] (eb : 𝒪 ≃+* 𝒪')
variable [Algebra 𝒪 Onr] [Algebra 𝒪' Onr'] (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (eb x))
variable {B : Type} [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B] (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))

include heO hB in

def toSrcψ (ψ : Onr' →ₐ[𝒪'] B) : Onr →ₐ[𝒪] B :=
  { toRingHom := (ψ : Onr' →+* B).comp (eO : Onr →+* Onr')
    commutes' := fun a => by
      show ψ (eO (algebraMap 𝒪 Onr a)) = algebraMap 𝒪 B a
      rw [heO, ψ.commutes, hB] }

include heO hB in

def ofSrcψ (ψ : Onr →ₐ[𝒪] B) : Onr' →ₐ[𝒪'] B :=
  { toRingHom := (ψ : Onr →+* B).comp (eO.symm : Onr' →+* Onr)
    commutes' := fun a => by
      show ψ (eO.symm (algebraMap 𝒪' Onr' a)) = algebraMap 𝒪' B a
      rw [← eb.apply_symm_apply a, ← heO, eO.symm_apply_apply, ψ.commutes, hB, eb.apply_symm_apply] }

@[scoped simp] theorem toSrcψ_apply (ψ : Onr' →ₐ[𝒪'] B) (y : Onr) : toSrcψ eO eb heO hB ψ y = ψ (eO y) := rfl
@[scoped simp] theorem ofSrcψ_apply (ψ : Onr →ₐ[𝒪] B) (y : Onr') : ofSrcψ eO eb heO hB ψ y = ψ (eO.symm y) := rfl

def toSrcG (x : ModuliPackage.GPoint 𝒪' (M' eO M) B) : ModuliPackage.GPoint 𝒪 M B :=
  ⟨toSrcψ eO eb heO hB x.ψ, x.nilp, x.pt⟩

theorem heq_map_id {ψ₁ ψ₂ : Onr →+* B} (hn : IsNilpotent (r : B)) (h : (RingHom.id B).comp ψ₂ = ψ₁) (m : M.obj B ψ₂ hn) :
    HEq (M.map hn hn (RingHom.id B) h m) m := by
  have : ψ₁ = ψ₂ := by rw [← h]; exact RingHom.id_comp _
  subst this
  exact heq_of_eq (M.map_id hn m)

def ofSrcG (x : ModuliPackage.GPoint 𝒪 M B) : ModuliPackage.GPoint 𝒪' (M' eO M) B :=
  ⟨ofSrcψ eO eb heO hB x.ψ, x.nilp,
    M.map (ψ' := ((ofSrcψ eO eb heO hB x.ψ : Onr' →+* B).comp (eO : Onr →+* Onr'))) x.nilp x.nilp (RingHom.id B)
      (RingHom.ext fun y => by simp) x.pt⟩

theorem toSrcG_ofSrcG (x : ModuliPackage.GPoint 𝒪 M B) : toSrcG eO eb heO hB (ofSrcG eO eb heO hB x) = x :=
  ModuliPackage.GPoint.ext' (AlgHom.ext fun y => by simp [toSrcG, ofSrcG]) (heq_map_id _ _ _)

theorem toSrcG_injective : Function.Injective (toSrcG (M := M) eO eb heO hB) := by
  intro x x' h
  have hpt := congr_arg_heq ModuliPackage.GPoint.pt h
  refine ModuliPackage.GPoint.ext' (AlgHom.ext fun y => ?_) hpt
  have := congrArg (fun z => (ModuliPackage.GPoint.ψ z) (eO.symm y)) h
  simpa [toSrcG] using this

theorem toSrcG_bijective : Function.Bijective (toSrcG (M := M) eO eb heO hB) :=
  ⟨toSrcG_injective eO eb heO hB, fun x => ⟨ofSrcG eO eb heO hB x, toSrcG_ofSrcG eO eb heO hB x⟩⟩

variable (Fr : Onr ≃ₐ[𝒪] Onr) (Fr' : Onr' ≃ₐ[𝒪'] Onr') (hFr : ∀ y, eO (Fr y) = Fr' (eO y))

include hFr in
theorem eO_Fr_pow (n : ℕ) (y : Onr) : eO ((Fr ^ n) y) = (Fr' ^ n) (eO y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, hFr]

include hFr in
theorem eO_Fr_zpow (n : ℤ) (y : Onr) : eO ((Fr ^ n) y) = (Fr' ^ n) (eO y) := by
  cases n with
  | ofNat n => simpa using eO_Fr_pow eO Fr Fr' hFr n y
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc, AlgEquiv.aut_inv, AlgEquiv.aut_inv, eq_comm, AlgEquiv.symm_apply_eq,
      ← eO_Fr_pow eO Fr Fr' hFr, AlgEquiv.apply_symm_apply]

include hFr in
theorem frobTwist_iff (n : ℤ) (ψ₁ ψ₂ : Onr' →ₐ[𝒪'] B) :
    ψ₂ = frobTwist Onr' Fr' n ψ₁ ↔ toSrcψ eO eb heO hB ψ₂ = frobTwist Onr Fr n (toSrcψ eO eb heO hB ψ₁) := by
  constructor
  · intro h
    subst h
    apply AlgHom.ext; intro y
    simp only [toSrcψ_apply, frobTwist, AlgHom.comp_apply, AlgEquiv.coe_algHom, eO_Fr_zpow eO Fr Fr' hFr]
  · intro h
    apply AlgHom.ext; intro y'
    obtain ⟨y, rfl⟩ := eO.surjective y'
    have := AlgHom.congr_fun h y
    simp only [toSrcψ_apply, frobTwist, AlgHom.comp_apply, AlgEquiv.coe_algHom] at this
    simp only [frobTwist, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    rw [← eO_Fr_zpow eO Fr Fr' hFr]
    exact this

theorem locallyLifts_iff (ψ₁ ψ₂ : Onr' →+* B) (hn : IsNilpotent (r : B))
    (m₁ : (M' eO M).obj B ψ₁ hn) (m₂ : (M' eO M).obj B ψ₂ hn)
    (Rel' : ∀ (L : Type) [CommRing L], (Onr' →+* L) → Rigidified r (Phi' eO Φ) L → Rigidified r (Phi' eO Φ) L → Prop)
    (Rel : ∀ (L : Type) [CommRing L], (Onr →+* L) → Rigidified r Φ L → Rigidified r Φ L → Prop)
    (hRel : ∀ (L : Type) [CommRing L] (χ : Onr' →+* L) (t t' : Rigidified r (Phi' eO Φ) L),
      Rel' L χ t t' ↔ Rel L (χ.comp (eO : Onr →+* Onr')) (toSrc eO t) (toSrc eO t')) :
    ModuliPackage.G.LocallyLifts (iota' eO ι) (Phi' eO Φ) (eta' eO η) ψ₁ ψ₂ hn m₁ m₂ Rel' ↔
      ModuliPackage.G.LocallyLifts ι Φ η (ψ₁.comp (eO : Onr →+* Onr')) (ψ₂.comp (eO : Onr →+* Onr')) hn m₁ m₂ Rel := by
  unfold ModuliPackage.G.LocallyLifts
  constructor
  · rintro ⟨n, f, hf, H⟩
    refine ⟨n, f, hf, fun i L _ _ _ hL => ?_⟩
    obtain ⟨t, t', h1, h2, h3, h4, h5⟩ := H i L hL
    exact ⟨toSrc eO t, toSrc eO t', (isAdmissible_iff eO ι ((algebraMap B L).comp ψ₁) t).1 h1,
      (isAdmissible_iff eO ι ((algebraMap B L).comp ψ₂) t').1 h2, h3, h4, (hRel L ((algebraMap B L).comp ψ₁) t t').1 h5⟩
  · rintro ⟨n, f, hf, H⟩
    refine ⟨n, f, hf, fun i L _ _ _ hL => ?_⟩
    obtain ⟨t, t', h1, h2, h3, h4, h5⟩ := H i L hL
    exact ⟨ofSrc eO t, ofSrc eO t', (isAdmissible_iff eO ι ((algebraMap B L).comp ψ₁) (ofSrc eO t)).2 h1,
      (isAdmissible_iff eO ι ((algebraMap B L).comp ψ₂) (ofSrc eO t')).2 h2, h3, h4,
      (hRel L ((algebraMap B L).comp ψ₁) (ofSrc eO t) (ofSrc eO t')).2 h5⟩

include hFr in
theorem G_isTranslate_iff (ε : Series (Onr ⧸ pIdeal r Onr)) (k m' : ℕ) (x x' : ModuliPackage.GPoint 𝒪' (M' eO M) B) :
    ModuliPackage.G.IsTranslate (iota' eO ι) (Phi' eO Φ) (eta' eO η) Fr'
        (ε.map ((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* _) : _ →+* Onr' ⧸ pIdeal r Onr')) k m' x x' ↔
      ModuliPackage.G.IsTranslate ι Φ η Fr ε k m' (toSrcG eO eb heO hB x) (toSrcG eO eb heO hB x') := by
  unfold ModuliPackage.G.IsTranslate
  refine and_congr (frobTwist_iff eO eb heO hB Fr Fr' hFr _ _ _) ?_
  exact locallyLifts_iff eO ι η _ _ _ _ _ _ _ (fun L _ χ t t' => rigidified_isTranslate_iff eO χ ε k m' t t')

include hFr in
theorem G_isPiTranslate_iff (x x' : ModuliPackage.GPoint 𝒪' (M' eO M) B) :
    ModuliPackage.G.IsPiTranslate (iota' eO ι) (Phi' eO Φ) (eta' eO η) Fr' x x' ↔
      ModuliPackage.G.IsPiTranslate ι Φ η Fr (toSrcG eO eb heO hB x) (toSrcG eO eb heO hB x') := by
  unfold ModuliPackage.G.IsPiTranslate
  refine and_congr (frobTwist_iff eO eb heO hB Fr Fr' hFr 1 _ _) ?_
  exact locallyLifts_iff eO ι η _ _ _ _ _ _ _ (fun L _ χ t t' => rigidified_isPiTranslate_iff eO χ t t')

variable [Algebra 𝒪 K₀] [Algebra 𝒪' K₀']

include hFr in
theorem G_isActBy_iff (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : ModuliPackage.GPoint 𝒪' (M' eO M) B) :
    ModuliPackage.G.IsActBy (iota' eO ι) (Phi' eO Φ) (eta' eO η) Fr' (E0' eO Φ eK E₀)
        (Matrix.GeneralLinearGroup.map (eK : K₀ →+* K₀') g) x x' ↔
      ModuliPackage.G.IsActBy ι Φ η Fr E₀ g (toSrcG eO eb heO hB x) (toSrcG eO eb heO hB x') := by
  unfold ModuliPackage.G.IsActBy
  constructor
  · rintro ⟨e', k, m', h1, h2, h3⟩
    refine ⟨(cCent eO Φ).symm e', k, m', ?_, ?_, ?_⟩
    · apply Matrix.map_injective eK.injective
      beta_reduce
      rw [← E0'_apply', h1, map_smul_natCast_pow, ← Matrix.GeneralLinearGroup.map_inv]
      rfl
    · have h2' : FormalODModule.HasKernelOfDegree
          (Series.map ((qbar (r := r) eO : Onr ⧸ pIdeal r Onr ≃+* _) : _ →+* Onr' ⧸ pIdeal r Onr')
            (MvFormalGroup.Hom.toPowerSeries (((cCent eO Φ).symm e' : Subring.centralizer _) : MvFormalGroup.End Φ.F)))
          (r ^ (2 * m')) := by
        rw [← cEnd_toPowerSeries, ← coe_cCent, RingEquiv.apply_symm_apply]; exact h2
      exact (hasKernelOfDegree_map_ringEquiv_iff _ _ _).1 h2'
    · rw [← G_isTranslate_iff eO ι η eb heO hB Fr Fr' hFr, ← cEnd_toPowerSeries, ← coe_cCent, RingEquiv.apply_symm_apply]
      exact h3
  · rintro ⟨e, k, m', h1, h2, h3⟩
    refine ⟨cCent eO Φ e, k, m', ?_, ?_, ?_⟩
    · rw [E0'_apply, h1, map_smul_natCast_pow, ← Matrix.GeneralLinearGroup.map_inv]
      rfl
    · rw [coe_cCent, cEnd_toPowerSeries]
      exact hasKernelOfDegree_map_ringEquiv _ _ _ h2
    · rw [coe_cCent, cEnd_toPowerSeries, G_isTranslate_iff eO ι η eb heO hB Fr Fr' hFr]
      exact h3

variable (π : 𝒪) (π' π₁ : 𝒪') (hπ₁ : eb π = π₁) (hspan : Ideal.span {π₁} = Ideal.span {π'})

@[reducible] def indAlg (C : Type) [CommRing C] [Algebra 𝒪' C] : Algebra 𝒪 C := ((algebraMap 𝒪' C).comp (eb : 𝒪 →+* 𝒪')).toAlgebra

include hB hπ₁ hspan in
theorem isNilpotent_of_frame (h : IsNilpotent (algebraMap 𝒪' B π')) : IsNilpotent (algebraMap 𝒪 B π) := by
  rw [hB, hπ₁]
  have hmem : π₁ ∈ Ideal.span {π'} := hspan ▸ Ideal.mem_span_singleton_self π₁
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [← ha, map_mul]
  exact Commute.isNilpotent_mul_left (Commute.all _ _) h

theorem isPullback_one_self {R K : Type} [CommRing R] [Field K] [Algebra R K] (ϖ : R) (C : Type) [CommRing C] [Algebra R C]
    (d : DeligneDatum (K := K) ϖ C) : DeligneDatum.IsPullback (K := K) (π := ϖ) C 1 d d := by
  have h := DeligneDatum.isPullback_pullback ϖ C (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ d
  have h1 : DeligneDatum.pullback ϖ C (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ d = d := (Omega.action K ϖ).act_one C d
  rw [h1, inv_one] at h
  exact h

variable (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ) (vdet' : Matrix.GeneralLinearGroup (Fin 2) K₀' →* Multiplicative ℤ)
variable
  (Ψ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B],
    (∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) → (OmegaNrObj (K := K₀) π Onr B ≃ OmegaNrObj (K := K₀') π₁ Onr' B))
  (Ξ : ∀ (B : Type) [CommRing B] [Algebra 𝒪' B], DeligneDatum (K := K₀') π₁ B ≃ DeligneDatum (K := K₀') π' B)

omit [Algebra 𝒪 B] in

def eTgtPt (eC : letI : Algebra 𝒪 B := indAlg eb B;
      (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (x : (ModuliPackage.G 𝒪' (M' eO M)).obj B) :
    (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).obj B :=
  letI : Algebra 𝒪 B := indAlg eb B
  ((Ψ B (fun _ => rfl) (eC (toSrcG eO eb heO (fun _ => rfl) x))).1,
    Ξ B (Ψ B (fun _ => rfl) (eC (toSrcG eO eb heO (fun _ => rfl) x))).2)

omit [Algebra 𝒪 B] in

def resAlgHom {B' : Type} [CommRing B'] [Algebra 𝒪' B'] (φ : B →ₐ[𝒪'] B') :
    letI : Algebra 𝒪 B := indAlg eb B; letI : Algebra 𝒪 B' := indAlg eb B'; B →ₐ[𝒪] B' :=
  letI : Algebra 𝒪 B := indAlg eb B; letI : Algebra 𝒪 B' := indAlg eb B'
  { toRingHom := (φ : B →+* B'), commutes' := fun a => φ.commutes (eb a) }

omit [Algebra 𝒪 B] in
theorem toSrcG_map {B' : Type} [CommRing B'] [Algebra 𝒪' B'] (φ : B →ₐ[𝒪'] B') (x : ModuliPackage.GPoint 𝒪' (M' eO M) B) :
    letI : Algebra 𝒪 B := indAlg eb B; letI : Algebra 𝒪 B' := indAlg eb B'
    toSrcG (M := M) eO eb heO (fun _ => rfl) (x.map φ) = (toSrcG eO eb heO (fun _ => rfl) x).map (resAlgHom eb φ) :=
  rfl

omit [Algebra 𝒪 B] in

theorem eTgtPt_nat
    (hΨ1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
      (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) (x : OmegaNrObj (K := K₀) π Onr B) (y : Onr'),
      (Ψ B hB x).1 y = x.1 (eO.symm y))
    (hΨbc : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
      (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
      (B₁ : Type) [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
      (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (eb x))
      (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (_ : ∀ b, f b = f' b)
      (x : OmegaNrObj (K := K₀) π Onr B) (x₁ : OmegaNrObj (K := K₀) π Onr B₁),
      DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f' (Ψ B hB x).2 (Ψ B₁ hB₁ x₁).2 ↔
        DeligneDatum.IsBaseChange (K := K₀) (π := π) f x.2 x₁.2)
    (hΞbc : ∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (B' : Type) [CommRing B'] [Algebra 𝒪' B'] (f : B →ₐ[𝒪'] B')
      (d : DeligneDatum (K := K₀') π₁ B) (d' : DeligneDatum (K := K₀') π₁ B'),
      DeligneDatum.IsBaseChange (K := K₀') (π := π') f (Ξ B d) (Ξ B' d') ↔
        DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f d d')
    {B' : Type} [CommRing B'] [Algebra 𝒪' B']
    (eC : letI : Algebra 𝒪 B := indAlg eb B;
      (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (eC' : letI : Algebra 𝒪 B' := indAlg eb B';
      (ModuliPackage.G 𝒪 M).obj B' → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B')
    (φ : B →ₐ[𝒪'] B')
    (hnat : letI : Algebra 𝒪 B := indAlg eb B; letI : Algebra 𝒪 B' := indAlg eb B';
      ∀ x : (ModuliPackage.G 𝒪 M).obj B,
        eC' ((ModuliPackage.G 𝒪 M).map (resAlgHom eb φ) x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (resAlgHom eb φ) (eC x))
    (x : (ModuliPackage.G 𝒪' (M' eO M)).obj B) :
    eTgtPt eO eb heO π π' π₁ Ψ Ξ eC' ((ModuliPackage.G 𝒪' (M' eO M)).map φ x) =
      (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).map φ (eTgtPt eO eb heO π π' π₁ Ψ Ξ eC x) := by
  letI : Algebra 𝒪 B := indAlg eb B
  letI : Algebra 𝒪 B' := indAlg eb B'
  set y := eC (toSrcG eO eb heO (fun _ => rfl) x) with hy
  have hy' : eC' (toSrcG (M := M) eO eb heO (fun _ => rfl) ((ModuliPackage.G 𝒪' (M' eO M)).map φ x)) =
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (resAlgHom eb φ) y := by
    rw [hy, ← hnat]
    rfl
  have h2 : (Ψ B' (fun _ => rfl) ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (resAlgHom eb φ) y)).2 =
      DeligneDatum.map π₁ φ (Ψ B (fun _ => rfl) y).2 :=
    DeligneDatum.ext' (funext fun Mx =>
      (hΨbc B (fun _ => rfl) B' (fun _ => rfl) (resAlgHom eb φ) φ (fun _ => rfl) y _).2
        (DeligneDatum.isBaseChange_map π (resAlgHom eb φ) y.2) Mx)
  have h3 : ∀ d : DeligneDatum (K := K₀') π₁ B, Ξ B' (DeligneDatum.map π₁ φ d) = DeligneDatum.map π' φ (Ξ B d) :=
    fun d => DeligneDatum.ext' (funext fun Mx => ((hΞbc B B' φ d (DeligneDatum.map π₁ φ d)).2
      (DeligneDatum.isBaseChange_map π₁ φ d) Mx))
  show ((Ψ B' (fun _ => rfl) (eC' (toSrcG eO eb heO (fun _ => rfl) ((ModuliPackage.G 𝒪' (M' eO M)).map φ x)))).1,
      Ξ B' (Ψ B' (fun _ => rfl) (eC' (toSrcG eO eb heO (fun _ => rfl) ((ModuliPackage.G 𝒪' (M' eO M)).map φ x)))).2) =
    (φ.comp (Ψ B (fun _ => rfl) y).1, DeligneDatum.map π' φ (Ξ B (Ψ B (fun _ => rfl) y).2))
  rw [hy', h2, h3]
  refine Prod.ext (AlgHom.ext fun y0 => ?_) rfl
  show (Ψ B' (fun _ => rfl) ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (resAlgHom eb φ) y)).1 y0 =
    φ ((Ψ B (fun _ => rfl) y).1 y0)
  rw [hΨ1, hΨ1]
  rfl

omit [Algebra 𝒪 B] in

theorem eTgtPt_bijective
    (eC : letI : Algebra 𝒪 B := indAlg eb B;
      (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (hbij : Function.Bijective eC) :
    Function.Bijective (eTgtPt (M := M) eO eb heO π π' π₁ Ψ Ξ eC) := by
  letI : Algebra 𝒪 B := indAlg eb B
  have : eTgtPt (M := M) eO eb heO π π' π₁ Ψ Ξ eC =
      (fun z => (z.1, Ξ B z.2)) ∘ (Ψ B (fun _ => rfl)) ∘ eC ∘ (toSrcG (M := M) eO eb heO (fun _ => rfl)) := rfl
  rw [this]
  exact (((Equiv.prodCongr (Equiv.refl _) (Ξ B)).bijective.comp (Ψ B _).bijective).comp hbij).comp
    (toSrcG_bijective eO eb heO _)

omit [Algebra 𝒪 B] in

theorem eTgtPt_fst
    (hΨ1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
      (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) (x : OmegaNrObj (K := K₀) π Onr B) (y : Onr'),
      (Ψ B hB x).1 y = x.1 (eO.symm y))
    (eC : letI : Algebra 𝒪 B := indAlg eb B;
      (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (hfst : letI : Algebra 𝒪 B := indAlg eb B; ∀ x : (ModuliPackage.G 𝒪 M).obj B, (eC x).1 = x.ψ)
    (x : (ModuliPackage.G 𝒪' (M' eO M)).obj B) :
    (eTgtPt eO eb heO π π' π₁ Ψ Ξ eC x).1 = x.ψ := by
  letI : Algebra 𝒪 B := indAlg eb B
  apply AlgHom.ext; intro y0
  show (Ψ B (fun _ => rfl) (eC (toSrcG eO eb heO (fun _ => rfl) x))).1 y0 = x.ψ y0
  rw [hΨ1, hfst]
  show x.ψ (eO (eO.symm y0)) = x.ψ y0
  rw [eO.apply_symm_apply]

omit [Algebra 𝒪 B] in
include hFr in

theorem eTgtPt_GL
    (hΨtw : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
      (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
      OmegaNr.IsTwistedAct π₁ Onr' Fr' vdet' B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x) (Ψ B hB x') ↔
        OmegaNr.IsTwistedAct π Onr Fr vdet B g x x')
    (hΞpb : ∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀')
      (d d' : DeligneDatum (K := K₀') π₁ B),
      DeligneDatum.IsPullback (K := K₀') (π := π') B g (Ξ B d) (Ξ B d') ↔
        DeligneDatum.IsPullback (K := K₀') (π := π₁) B g d d')
    (eC : letI : Algebra 𝒪 B := indAlg eb B;
      (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (hGL : letI : Algebra 𝒪 B := indAlg eb B;
      ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 M).obj B),
        ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (eC x) (eC x'))
    (g' : Matrix.GeneralLinearGroup (Fin 2) K₀') (x x' : (ModuliPackage.G 𝒪' (M' eO M)).obj B) :
    ModuliPackage.G.IsActBy (iota' eO ι) (Phi' eO Φ) (eta' eO η) Fr' (E0' eO Φ eK E₀) g' x x' ↔
      OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B g' (eTgtPt eO eb heO π π' π₁ Ψ Ξ eC x)
        (eTgtPt eO eb heO π π' π₁ Ψ Ξ eC x') := by
  letI : Algebra 𝒪 B := indAlg eb B
  obtain ⟨g, rfl⟩ : ∃ g, g' = Matrix.GeneralLinearGroup.map (eK : K₀ →+* K₀') g :=
    ⟨Matrix.GeneralLinearGroup.map (eK.symm : K₀' →+* K₀) g', by ext i j; simp⟩
  rw [G_isActBy_iff (eO := eO) (ι := ι) (η := η) (eK := eK) (E₀ := E₀) (eb := eb) (heO := heO) (hB := fun _ => rfl)
    (Fr := Fr) (Fr' := Fr') (hFr := hFr), hGL, ← hΨtw B (fun _ => rfl) g]
  exact and_congr Iff.rfl (hΞpb B _ _ _).symm

omit [Algebra 𝒪 B] in
include hFr in

theorem eTgtPt_Pi
    (hΨ1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
      (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) (x : OmegaNrObj (K := K₀) π Onr B) (y : Onr'),
      (Ψ B hB x).1 y = x.1 (eO.symm y))
    (hΨpb : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
      (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
      DeligneDatum.IsPullback (K := K₀') (π := π₁) B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x).2 (Ψ B hB x').2 ↔
        DeligneDatum.IsPullback (K := K₀) (π := π) B g x.2 x'.2)
    (eC : letI : Algebra 𝒪 B := indAlg eb B;
      (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)
    (hPi : letI : Algebra 𝒪 B := indAlg eb B;
      ∀ (x x' : (ModuliPackage.G 𝒪 M).obj B),
        ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → eC x' = (frobTwist Onr Fr 1 (eC x).1, (eC x).2))
    (x x' : (ModuliPackage.G 𝒪' (M' eO M)).obj B) :
    ModuliPackage.G.IsPiTranslate (iota' eO ι) (Phi' eO Φ) (eta' eO η) Fr' x x' →
      eTgtPt eO eb heO π π' π₁ Ψ Ξ eC x' =
        (frobTwist Onr' Fr' 1 (eTgtPt eO eb heO π π' π₁ Ψ Ξ eC x).1, (eTgtPt eO eb heO π π' π₁ Ψ Ξ eC x).2) := by
  letI : Algebra 𝒪 B := indAlg eb B
  intro h
  rw [G_isPiTranslate_iff (eO := eO) (ι := ι) (η := η) (eb := eb) (heO := heO) (hB := fun _ => rfl) (Fr := Fr) (Fr' := Fr')
    (hFr := hFr)] at h
  have h1 := hPi _ _ h
  set y := eC (toSrcG eO eb heO (fun _ => rfl) x) with hy
  have h2 : (Ψ B (fun _ => rfl) (frobTwist Onr Fr 1 y.1, y.2)).2 = (Ψ B (fun _ => rfl) y).2 := by
    have hpb := (hΨpb B (fun _ => rfl) 1 y (frobTwist Onr Fr 1 y.1, y.2)).2 (isPullback_one_self π B y.2)
    rw [map_one] at hpb
    have hpb' := isPullback_one_self π₁ B (Ψ B (fun _ => rfl) y).2
    exact DeligneDatum.ext' (funext fun Mx => by rw [hpb Mx, hpb' Mx])
  show ((Ψ B (fun _ => rfl) (eC (toSrcG eO eb heO (fun _ => rfl) x'))).1,
      Ξ B (Ψ B (fun _ => rfl) (eC (toSrcG eO eb heO (fun _ => rfl) x'))).2) =
    (frobTwist Onr' Fr' 1 (Ψ B (fun _ => rfl) y).1, Ξ B (Ψ B (fun _ => rfl) y).2)
  rw [h1]
  refine Prod.ext (AlgHom.ext fun y0 => ?_) (congrArg (Ξ B) h2)
  show (Ψ B (fun _ => rfl) (frobTwist Onr Fr 1 y.1, y.2)).1 y0 = frobTwist Onr' Fr' 1 (Ψ B (fun _ => rfl) y).1 y0
  rw [hΨ1]
  simp only [frobTwist, AlgHom.comp_apply, AlgEquiv.coe_algHom]
  rw [hΨ1]
  congr 1
  apply eO.injective
  rw [eO_Fr_zpow eO Fr Fr' hFr, eO.apply_symm_apply, eO.apply_symm_apply]

omit [Algebra 𝒪 B] in
include eb heO hFr in

theorem G_piTotalPt
    (hPitot : letI : Algebra 𝒪 B := indAlg eb B; ∀ (x : (ModuliPackage.G 𝒪 M).obj B),
      ∃ x' : (ModuliPackage.G 𝒪 M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x')
    (x : (ModuliPackage.G 𝒪' (M' eO M)).obj B) :
    ∃ x' : (ModuliPackage.G 𝒪' (M' eO M)).obj B, ModuliPackage.G.IsPiTranslate (iota' eO ι) (Phi' eO Φ) (eta' eO η) Fr' x x' := by
  letI : Algebra 𝒪 B := indAlg eb B
  obtain ⟨x₀, h⟩ := hPitot (toSrcG (M := M) eO eb heO (fun _ => rfl) x)
  refine ⟨ofSrcG eO eb heO (fun _ => rfl) x₀, ?_⟩
  rw [G_isPiTranslate_iff (eO := eO) (ι := ι) (η := η) (eb := eb) (heO := heO) (hB := fun _ => rfl) (Fr := Fr) (Fr' := Fr')
    (hFr := hFr), toSrcG_ofSrcG]
  exact h

end Frame

end R4F4b
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing.R4F4b"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing.R4F4b"

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (𝒪' : Type) [CommRing 𝒪'] (K₀' : Type) [Field K₀'] [Algebra 𝒪' K₀'] (π' : 𝒪')
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (vdet' : Matrix.GeneralLinearGroup (Fin 2) K₀' →* Multiplicative ℤ)

    (eb : 𝒪 ≃+* 𝒪') (eK : K₀ ≃+* K₀') (hcomm : ∀ x : 𝒪, eK (algebraMap 𝒪 K₀ x) = algebraMap 𝒪' K₀' (eb x))
    (π₁ : 𝒪') (hπ₁ : eb π = π₁) (hspan : Ideal.span {π₁} = Ideal.span {π'})
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (eb x))
    (hFr : ∀ y, eO (Fr y) = Fr' (eO y))
    (hv : ∀ g, vdet' (Matrix.GeneralLinearGroup.map eK.toRingHom g) = vdet g)

    (hΨ :
      ∃ (Ψ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B],
          (∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) →
            (OmegaNrObj (K := K₀) π Onr B ≃ OmegaNrObj (K := K₀') π₁ Onr' B)),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (x : OmegaNrObj (K := K₀) π Onr B) (y : Onr'), (Ψ B hB x).1 y = x.1 (eO.symm y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
          OmegaNr.IsTwistedAct π₁ Onr' Fr' vdet' B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x) (Ψ B hB x') ↔
            OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
          DeligneDatum.IsPullback (K := K₀') (π := π₁) B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x).2 (Ψ B hB x').2 ↔
            DeligneDatum.IsPullback (K := K₀) (π := π) B g x.2 x'.2) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (B₁ : Type) [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
            (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (eb x))
            (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (_ : ∀ b, f b = f' b)
            (x : OmegaNrObj (K := K₀) π Onr B) (x₁ : OmegaNrObj (K := K₀) π Onr B₁),
          DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f' (Ψ B hB x).2 (Ψ B₁ hB₁ x₁).2 ↔
            DeligneDatum.IsBaseChange (K := K₀) (π := π) f x.2 x₁.2))

    (hΞ :
      ∃ Ξ : ∀ (B : Type) [CommRing B] [Algebra 𝒪' B], DeligneDatum (K := K₀') π₁ B ≃ DeligneDatum (K := K₀') π' B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (d : DeligneDatum (K := K₀') π₁ B), (Ξ B d).line = d.line) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀')
            (d d' : DeligneDatum (K := K₀') π₁ B),
          DeligneDatum.IsPullback (K := K₀') (π := π') B g (Ξ B d) (Ξ B d') ↔
            DeligneDatum.IsPullback (K := K₀') (π := π₁) B g d d') ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (B' : Type) [CommRing B'] [Algebra 𝒪' B'] (f : B →ₐ[𝒪'] B')
            (d : DeligneDatum (K := K₀') π₁ B) (d' : DeligneDatum (K := K₀') π₁ B'),
          DeligneDatum.IsBaseChange (K := K₀') (π := π') f (Ξ B d) (Ξ B' d') ↔
            DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f d d'))

    (hpkg :
      ∃ (ι : Zp2 r →+* Onr)
        (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
        (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
        (_ : Φ.HasHeight 4)
        (M : ModuliPackage.{0, 0} r Onr) (_ : M.IsZariskiSheaf)
        (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
          Rigidified r Φ B → M.obj B ψ hB)
        (_ : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
              (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
              (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
          (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
              (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
              (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
              η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
          (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
              ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
                ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
                  (hL : IsNilpotent (r : L)),
                  ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                    η L ((algebraMap B L).comp ψ) hL t =
                      M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
        (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
        (_ : Function.Injective E₀ ∧
          ∃ m : ℕ,
            (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
            (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))
        (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
            (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 M).obj B), e B' hB' ((ModuliPackage.G 𝒪 M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (e B hB x)) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (e B hB)) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 M).obj B), (e B hB x).1 = x.ψ) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 M).obj B),
            ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (e B hB x) (e B hB x')) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 M).obj B),
            ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist Onr Fr 1 (e B hB x).1, (e B hB x).2)) ∧

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 M).obj B), ∃ x' : (ModuliPackage.G 𝒪 M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x'))
    :
    ∃ (ι : Zp2 r →+* Onr')
      (Φ : FormalODModule r (Onr' ⧸ pIdeal r Onr'))
      (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr')).comp ι))
      (_ : Φ.HasHeight 4)
      (M : ModuliPackage.{0, 0} r Onr') (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)),
        Rigidified r Φ B → M.obj B ψ hB)
      (_ : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B))
            (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
            (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
        (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr' →+* B) (ψ' : Onr' →+* B')
            (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
            (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
            η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
            ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
              ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
                (hL : IsNilpotent (r : L)),
                ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                  η L ((algebraMap B L).comp ψ) hL t =
                    M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀')
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) 𝒪', ∃ e, E₀ e = (r : K₀') ^ m • A.map (algebraMap 𝒪' K₀')) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪', (r : K₀') ^ m • E₀ e = A.map (algebraMap 𝒪' K₀')))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B], IsNilpotent (algebraMap 𝒪' B π') → (ModuliPackage.G 𝒪' M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪' B'] (hB : IsNilpotent (algebraMap 𝒪' B π')) (hB' : IsNilpotent (algebraMap 𝒪' B' π'))
          (φ : B →ₐ[𝒪'] B') (x : (ModuliPackage.G 𝒪' M).obj B), e B' hB' ((ModuliPackage.G 𝒪' M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (x : (ModuliPackage.G 𝒪' M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (g : Matrix.GeneralLinearGroup (Fin 2) K₀') (x x' : (ModuliPackage.G 𝒪' M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr' E₀ g x x' ↔ OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (x x' : (ModuliPackage.G 𝒪' M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x' → e B hB x' = (frobTwist Onr' Fr' 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (x : (ModuliPackage.G 𝒪' M).obj B), ∃ x' : (ModuliPackage.G 𝒪' M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x') := by
  obtain ⟨Ψ, hΨ1, hΨtw, hΨpb, hΨbc⟩ := hΨ
  obtain ⟨Ξ, -, hΞpb, hΞbc⟩ := hΞ
  obtain ⟨ι, Φ, hΦ, hΦ4, M, hM, η, ⟨hη1, hη2, hη3⟩, E₀, ⟨hE₀, m, hm₁, hm₂⟩, e, hnat, hbij, hfst, hGL, hPi, hPitot⟩ := hpkg
  refine ⟨R4F4b.iota' eO ι, R4F4b.Phi' eO Φ, ?_, R4F4b.hasHeight_map_ringEquiv _ Φ 4 hΦ4, R4F4b.M' eO M,
    R4F4b.isZariskiSheaf_M' eO M hM, R4F4b.eta' eO η, ⟨?_, ?_, ?_⟩, R4F4b.E0' eO Φ eK E₀,
    ⟨R4F4b.E0'_injective eO Φ eK E₀ hE₀, m, R4F4b.E0'_comm eO Φ eK E₀ eb hcomm m hm₁ hm₂⟩,
    fun B _ _ _ hB x =>
      letI : Algebra 𝒪 B := R4F4b.indAlg eb B
      R4F4b.eTgtPt (M := M) (eO := eO) (eb := eb) (heO := heO) (π := π) (π' := π') (π₁ := π₁) (Ψ := Ψ) (Ξ := Ξ)
        (e B (R4F4b.isNilpotent_of_frame eb (fun _ => rfl) π π' π₁ hπ₁ hspan hB)) x,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [R4F4b.mk_comp_iota']
    exact R4F4b.isSpecial_map_ringEquiv _ _ Φ hΦ
  · intro B _ _ ψ hB t t' ht ht'
    exact R4F4b.eta'_law1 eO ι η ψ hB (hη1 B _ hB) t t' ht ht'
  · intro B B' _ _ _ _ ψ ψ' hB hB' f hf t ht
    exact R4F4b.eta'_law2 eO ι η ψ ψ' hB hB' f hf (fun hf₀ t₀ ht₀ => hη2 B B' _ _ hB hB' f hf₀ t₀ ht₀) t ht
  · intro B _ _ ψ hB m
    exact R4F4b.eta'_law3N eO ι η ψ hB m (hη3 B _ hB m)
  · intro B _ _ _ B' _ _ _ hB hB' φ x
    letI : Algebra 𝒪 B := R4F4b.indAlg eb B
    letI : Algebra 𝒪 B' := R4F4b.indAlg eb B'
    exact R4F4b.eTgtPt_nat (M := M) (eO := eO) (eb := eb) (heO := heO) (π := π) (π' := π') (π₁ := π₁) (Ψ := Ψ) (Ξ := Ξ) hΨ1 hΨbc hΞbc _ _ φ
      (fun y => hnat B B' _ _ (R4F4b.resAlgHom eb φ) y) x
  · intro B _ _ _ hB
    letI : Algebra 𝒪 B := R4F4b.indAlg eb B
    exact R4F4b.eTgtPt_bijective (M := M) (eO := eO) (eb := eb) (heO := heO) (π := π) (π' := π') (π₁ := π₁) (Ψ := Ψ) (Ξ := Ξ) _ (hbij B _)
  · intro B _ _ _ hB x
    letI : Algebra 𝒪 B := R4F4b.indAlg eb B
    exact R4F4b.eTgtPt_fst (M := M) (eO := eO) (eb := eb) (heO := heO) (π := π) (π' := π') (π₁ := π₁) (Ψ := Ψ) (Ξ := Ξ) hΨ1 _ (hfst B _) x
  · intro B _ _ _ hB g x x'
    letI : Algebra 𝒪 B := R4F4b.indAlg eb B
    exact R4F4b.eTgtPt_GL (M := M) (eO := eO) (ι := ι) (η := η) (eK := eK) (E₀ := E₀) (eb := eb) (heO := heO) (Fr := Fr) (Fr' := Fr') (hFr := hFr) (π := π) (π' := π') (π₁ := π₁) (vdet := vdet) (vdet' := vdet') (Ψ := Ψ) (Ξ := Ξ) hΨtw hΞpb _ (hGL B _) g x x'
  · intro B _ _ _ hB x x'
    letI : Algebra 𝒪 B := R4F4b.indAlg eb B
    exact R4F4b.eTgtPt_Pi (M := M) (eO := eO) (ι := ι) (η := η) (eK := eK) (eb := eb) (heO := heO) (Fr := Fr) (Fr' := Fr') (hFr := hFr) (π := π) (π' := π') (π₁ := π₁) (Ψ := Ψ) (Ξ := Ξ) hΨ1 hΨpb _ (hPi B _) x x'
  · intro B _ _ _ x
    letI : Algebra 𝒪 B := R4F4b.indAlg eb B
    exact R4F4b.G_piTotalPt (M := M) (eO := eO) (ι := ι) (η := η) (eb := eb) (heO := heO) (Fr := Fr) (Fr' := Fr') (hFr := hFr) (hPitot B) x

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing (solution)
