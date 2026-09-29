-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.existsUnique_glue_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ee4c4ba8-835e-50c5-82b0-1fb3014b7145

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_Module_Invertible_of_localization_maximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcOmegaGlue

section BC

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {R : Type} [CommRing R] [Algebra 𝒪 R]

abbrev bcT (A : Type) [CommRing A] [Algebra 𝒪 A] [Algebra R A] [IsScalarTower 𝒪 R A] (L : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K R L →ₗ[R] latticeBaseChange 𝒪 K A L :=
  AlgebraTensorModule.rTensor 𝒪 (↥L.1) (Algebra.linearMap R A)

variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra R A] [IsScalarTower 𝒪 R A]

theorem bcT_tmul (L : FullLattice 𝒪 K) (r : R) (v : ↥L.1) :
    bcT (𝒪 := 𝒪) (R := R) A L (r ⊗ₜ[𝒪] v) = algebraMap R A r ⊗ₜ[𝒪] v := rfl

theorem rTensor_toAlgHom_apply (L : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K R L) :
    LinearMap.rTensor (↥L.1) (IsScalarTower.toAlgHom 𝒪 R A).toLinearMap x = bcT A L x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearMap.map_zero]
  | add a b ha hb => rw [LinearMap.map_add, LinearMap.map_add, ha, hb]
  | tmul r v => rfl

theorem lineBaseChange_eq_localized' (S : Submonoid R) [IsLocalization S A] (L : FullLattice 𝒪 K)
    (N : Submodule R (latticeBaseChange 𝒪 K R L)) :
    lineBaseChange (IsScalarTower.toAlgHom 𝒪 R A) L N = N.localized' A S (bcT A L) := by
  rw [Submodule.localized'_eq_span, lineBaseChange]
  congr 1

theorem map_line_eq_localized' (S : Submonoid R) [IsLocalization S A] (δ : DeligneDatum (K := K) π R)
    (L : FullLattice 𝒪 K) :
    ((Omega K π).map (IsScalarTower.toAlgHom 𝒪 R A) δ).line L = (δ.line L).localized' A S (bcT A L) :=
  lineBaseChange_eq_localized' S L (δ.line L)

theorem bcT_mem_localized'_iff (S : Submonoid R) [IsLocalization S A] (L : FullLattice 𝒪 K)
    (N : Submodule R (latticeBaseChange 𝒪 K R L)) (x : latticeBaseChange 𝒪 K R L) :
    bcT A L x ∈ N.localized' A S (bcT A L) ↔ ∃ s : S, (s : R) • x ∈ N := by
  have key : bcT A L x ∈ N.localized' A S (bcT A L) ↔ N.toLocalizedQuotient' A S (bcT A L) (Submodule.Quotient.mk x) = 0 := by
    rw [Submodule.toLocalizedQuotient'_mk, Submodule.Quotient.mk_eq_zero]
  rw [key, IsLocalizedModule.eq_zero_iff S (N.toLocalizedQuotient' A S (bcT A L))]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hs
    exact hs
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hs

theorem bcT_mem_localized'_of_mem (S : Submonoid R) [IsLocalization S A] (L : FullLattice 𝒪 K)
    (N : Submodule R (latticeBaseChange 𝒪 K R L)) {x : latticeBaseChange 𝒪 K R L} (hx : x ∈ N) :
    bcT A L x ∈ N.localized' A S (bcT A L) := by
  rw [Submodule.localized'_eq_span]
  exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem bcT_bcT (A' : Type) [CommRing A'] [Algebra 𝒪 A'] [Algebra R A'] [IsScalarTower 𝒪 R A']
    [Algebra A A'] [IsScalarTower 𝒪 A A'] [IsScalarTower R A A']
    (L : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K R L) :
    bcT (R := A) A' L (bcT (R := R) A L x) = bcT (R := R) A' L x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
  | add a b ha hb => rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ha, hb]
  | tmul r v => rw [bcT_tmul, bcT_tmul, bcT_tmul, ← IsScalarTower.algebraMap_apply]

theorem bcT_smul' (L : FullLattice 𝒪 K) (r : R) (x : latticeBaseChange 𝒪 K R L) :
    bcT A L (r • x) = algebraMap R A r • bcT A L x := by
  rw [LinearMap.map_smul, algebraMap_smul]

theorem bcT_inclBaseChange {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) (x : latticeBaseChange 𝒪 K R M') :
    bcT A M (inclBaseChange R h x) = inclBaseChange A h (bcT A M' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero]
  | add a b ha hb => simp only [LinearMap.map_add, ha, hb]
  | tmul r v => rfl

theorem bcT_actBaseChange (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K)
    (x : latticeBaseChange 𝒪 K R M) :
    bcT A (FullLattice.act g M) (actBaseChange R g M x) = actBaseChange A g M (bcT A M x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearEquiv.map_zero]
  | add a b ha hb => rw [LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, LinearEquiv.map_add, ha, hb]
  | tmul r v => rfl

theorem bcT_mem_smul_top (L : FullLattice 𝒪 K) (𝔭 : Ideal R) (𝔮 : Ideal A) (h𝔭 : 𝔭 ≤ 𝔮.comap (algebraMap R A))
    {z : latticeBaseChange 𝒪 K R L} (hz : z ∈ (𝔭 • ⊤ : Submodule R (latticeBaseChange 𝒪 K R L))) :
    bcT A L z ∈ (𝔮 • ⊤ : Submodule A (latticeBaseChange 𝒪 K A L)) := by
  refine Submodule.smul_induction_on (p := fun z => bcT A L z ∈ (𝔮 • ⊤ : Submodule A (latticeBaseChange 𝒪 K A L))) hz
    (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · show bcT A L (r • n) ∈ _
    rw [bcT_smul']
    exact Submodule.smul_mem_smul (h𝔭 hr) Submodule.mem_top
  · show bcT A L (x + y) ∈ _
    rw [LinearMap.map_add]; exact Submodule.add_mem _ hx hy

end BC

section AwayTower

variable {B : Type} [CommRing B] {C D : Type} [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
  [Algebra C D] [IsScalarTower B C D]

theorem away_algebraMap_of_away_mul (f g : B) [IsLocalization.Away g C] [IsLocalization.Away (f * g) D] :
    IsLocalization.Away (algebraMap B C f) D := by
  let T := Localization.Away (algebraMap B C f)
  haveI : IsLocalization.Away (f * g) T := inferInstance
  let e : T ≃ₐ[B] D := IsLocalization.algEquiv (Submonoid.powers (f * g)) T D
  have hcomp : (e : T →ₐ[B] D).comp (IsScalarTower.toAlgHom B C T) = IsScalarTower.toAlgHom B C D :=
    Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers g)) _ _
  have hce : ∀ c : C, e (algebraMap C T c) = algebraMap C D c := fun c => by
    have := congrArg (fun φ : C →ₐ[B] D => φ c) hcomp
    simpa using this
  let e' : T ≃ₐ[C] D := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) hce
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap B C f)) e'

end AwayTower

section InvLocal

variable {R : Type} [CommRing R] {P : Type} [AddCommGroup P] [Module R P]

theorem invertible_localizedModule_of_away (r : R) (A : Type) [CommRing A] [Algebra R A] [IsLocalization.Away r A]
    (Pr : Type) [AddCommGroup Pr] [Module R Pr] [Module A Pr] [IsScalarTower R A Pr] (g : P →ₗ[R] Pr)
    [IsLocalizedModule (Submonoid.powers r) g] (h : Module.Invertible A Pr)
    (S : Submonoid R) (hr : r ∈ S) :
    Module.Invertible (Localization S) (LocalizedModule S P) := by
  set Lc := Localization S
  have hu : IsUnit (algebraMap R Lc r) := IsLocalization.map_units Lc ⟨r, hr⟩
  let φ : A →+* Lc := IsLocalization.Away.lift r hu
  letI : Algebra A Lc := φ.toAlgebra
  haveI : IsScalarTower R A Lc := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap R Lc x = φ (algebraMap R A x)
    rw [IsLocalization.Away.lift_eq]
  haveI := h
  have e3 : A ⊗[R] P ≃ₗ[A] Pr := (IsLocalizedModule.isBaseChange (Submonoid.powers r) A g).equiv
  have h1 : Module.Invertible Lc (Lc ⊗[A] (A ⊗[R] P)) :=
    Module.Invertible.congr (LinearEquiv.baseChange A Lc _ _ e3).symm
  have e2 : Lc ⊗[A] (A ⊗[R] P) ≃ₗ[Lc] Lc ⊗[R] P := AlgebraTensorModule.cancelBaseChange R A Lc Lc P
  have h2 : Module.Invertible Lc (Lc ⊗[R] P) := by
    haveI := h1
    exact Module.Invertible.congr e2
  have e1 : Lc ⊗[R] P ≃ₗ[Lc] LocalizedModule S P :=
    (IsLocalizedModule.isBaseChange S Lc (LocalizedModule.mkLinearMap S P)).equiv
  haveI := h2
  exact Module.Invertible.congr e1

theorem invertible_of_cover {k : ℕ} (f : Fin k → R) (hf : Ideal.span (Set.range f) = ⊤)
    (A : Fin k → Type) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, IsLocalization.Away (f i) (A i)]
    (Pl : Fin k → Type) [∀ i, AddCommGroup (Pl i)] [∀ i, Module R (Pl i)] [∀ i, Module (A i) (Pl i)]
    [∀ i, IsScalarTower R (A i) (Pl i)] (g : ∀ i, P →ₗ[R] Pl i) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (g i)]
    (h : ∀ i, Module.Invertible (A i) (Pl i)) :
    Module.Invertible R P := by
  classical

  let s : Set R := Set.range f
  let idx : ↥s → Fin k := fun r => r.2.choose
  have hidx : ∀ r : ↥s, f (idx r) = (r : R) := fun r => r.2.choose_spec
  haveI hA : ∀ r : ↥s, IsLocalization.Away (r : R) (A (idx r)) := fun r =>
    hidx r ▸ (inferInstance : IsLocalization.Away (f (idx r)) (A (idx r)))
  haveI hg : ∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r : R)) (g (idx r)) := fun r =>
    hidx r ▸ (inferInstance : IsLocalizedModule (Submonoid.powers (f (idx r))) (g (idx r)))
  haveI : Module.FinitePresentation R P := by
    refine Module.FinitePresentation.of_localizationSpan' s hf (Rₚ := fun r => A (idx r)) (Mₚ := fun r => Pl (idx r))
      (fun r => g (idx r)) (fun r => ?_)
    haveI := h (idx r)
    exact Module.finitePresentation_of_projective _ _
  apply Module.Invertible.of_localization_maximal
  intro 𝔪 h𝔪
  have hex : ∃ i, f i ∉ 𝔪 := by
    by_contra hcon
    push Not at hcon
    have hle : Ideal.span (Set.range f) ≤ 𝔪 := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
    rw [hf] at hle
    exact h𝔪.ne_top (top_le_iff.mp hle)
  obtain ⟨i, hi⟩ := hex
  exact invertible_localizedModule_of_away (f i) (A i) (Pl i) (g i) (h i) 𝔪.primeCompl hi

end InvLocal

section Membership

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem mem_of_forall_pow_smul_mem {k : ℕ} (f : Fin k → R) (hf : Ideal.span (Set.range f) = ⊤)
    (N : Submodule R V) (x : V) (h : ∀ i, ∃ n : ℕ, (f i ^ n) • x ∈ N) : x ∈ N := by
  classical
  choose n hn using h
  let M : ℕ := Finset.univ.sup n
  have hM : ∀ i, (f i ^ M) • x ∈ N := fun i => by
    have hle : n i ≤ M := Finset.le_sup (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact N.smul_mem _ (hn i)
  have htop : Ideal.span (Set.range fun i => f i ^ M) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range f) hf M
    rwa [← Set.range_comp] at this
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => f i ^ M) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  rw [← one_smul R x, ← hc, Finset.sum_smul]
  refine N.sum_mem fun i _ => ?_
  rw [mul_smul]
  exact N.smul_mem _ (hM i)

end Membership

section Pair

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem exists_pow_smul_bcT_mem
    {Ci Cj D : Type} [CommRing Ci] [CommRing Cj] [CommRing D]
    [Algebra 𝒪 Ci] [Algebra B Ci] [IsScalarTower 𝒪 B Ci]
    [Algebra 𝒪 Cj] [Algebra B Cj] [IsScalarTower 𝒪 B Cj]
    [Algebra 𝒪 D] [Algebra B D] [IsScalarTower 𝒪 B D]
    (fi fj : B) [IsLocalization.Away fi Ci] [IsLocalization.Away fj Cj] [IsLocalization.Away (fi * fj) D]
    (ρ₁ : Ci →ₐ[B] D) (ρ₂ : Cj →ₐ[B] D) (di : DeligneDatum (K := K) π Ci) (dj : DeligneDatum (K := K) π Cj)
    (hd : (Omega K π).map (ρ₁.restrictScalars 𝒪) di = (Omega K π).map (ρ₂.restrictScalars 𝒪) dj)
    (L : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B L) (hx : bcT Ci L x ∈ di.line L) :
    ∃ n : ℕ, bcT Cj L ((fi ^ n) • x) ∈ dj.line L := by
  letI algi : Algebra Ci D := ρ₁.toRingHom.toAlgebra
  letI algj : Algebra Cj D := ρ₂.toRingHom.toAlgebra
  haveI : IsScalarTower B Ci D := IsScalarTower.of_algebraMap_eq fun b => (ρ₁.commutes b).symm
  haveI : IsScalarTower B Cj D := IsScalarTower.of_algebraMap_eq fun b => (ρ₂.commutes b).symm
  haveI : IsScalarTower 𝒪 Ci D := IsScalarTower.of_algebraMap_eq fun o => by
    show algebraMap 𝒪 D o = ρ₁ (algebraMap 𝒪 Ci o)
    rw [IsScalarTower.algebraMap_apply 𝒪 B Ci, ρ₁.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower 𝒪 Cj D := IsScalarTower.of_algebraMap_eq fun o => by
    show algebraMap 𝒪 D o = ρ₂ (algebraMap 𝒪 Cj o)
    rw [IsScalarTower.algebraMap_apply 𝒪 B Cj, ρ₂.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization.Away (algebraMap B Cj fi) D := away_algebraMap_of_away_mul fi fj
  have eρ₁ : IsScalarTower.toAlgHom 𝒪 Ci D = ρ₁.restrictScalars 𝒪 := AlgHom.ext fun _ => rfl
  have eρ₂ : IsScalarTower.toAlgHom 𝒪 Cj D = ρ₂.restrictScalars 𝒪 := AlgHom.ext fun _ => rfl

  have h1 : bcT (R := Ci) D L (bcT Ci L x) ∈ ((Omega K π).map (ρ₁.restrictScalars 𝒪) di).line L := by
    rw [← eρ₁]
    show _ ∈ lineBaseChange (IsScalarTower.toAlgHom 𝒪 Ci D) L (di.line L)
    rw [lineBaseChange]
    exact Submodule.subset_span ⟨_, hx, rTensor_toAlgHom_apply L _⟩

  rw [hd, ← eρ₂, map_line_eq_localized' π (Submonoid.powers (algebraMap B Cj fi)) dj L, bcT_bcT,
    ← bcT_bcT (R := B) (A := Cj) D L x] at h1
  obtain ⟨⟨_, n, rfl⟩, hs⟩ :=
    (bcT_mem_localized'_iff (Submonoid.powers (algebraMap B Cj fi)) L (dj.line L) (bcT Cj L x)).mp h1
  refine ⟨n, ?_⟩
  rw [bcT_smul', map_pow]
  exact hs

end Pair

section Glue

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]
variable {k : ℕ} (f : Fin k → B)
variable (C : Fin k → Type) [∀ i, CommRing (C i)] [∀ i, Algebra 𝒪 (C i)] [∀ i, Algebra B (C i)]
  [∀ i, IsScalarTower 𝒪 B (C i)]
variable (d : ∀ i, DeligneDatum (K := K) π (C i))

def glueLine (L : FullLattice 𝒪 K) : Submodule B (latticeBaseChange 𝒪 K B L) :=
  ⨅ i, (((d i).line L).restrictScalars B).comap (bcT (C i) L)

variable {B f C d}

theorem mem_glueLine {L : FullLattice 𝒪 K} {x : latticeBaseChange 𝒪 K B L} :
    x ∈ glueLine π B C d L ↔ ∀ i, bcT (C i) L x ∈ (d i).line L := by
  simp only [glueLine, Submodule.mem_iInf, Submodule.mem_comap, Submodule.restrictScalars_mem]

variable [∀ i, IsLocalization.Away (f i) (C i)]
variable {C₂ : Fin k → Fin k → Type} [∀ i j, CommRing (C₂ i j)] [∀ i j, Algebra 𝒪 (C₂ i j)] [∀ i j, Algebra B (C₂ i j)]
  [∀ i j, IsScalarTower 𝒪 B (C₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (C₂ i j)]
  {ρ₁ : ∀ i j, C i →ₐ[B] C₂ i j} {ρ₂ : ∀ i j, C j →ₐ[B] C₂ i j}

theorem exists_pow_smul_mem_glueLine
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j))
    (L : FullLattice 𝒪 K) (i : Fin k) (x : latticeBaseChange 𝒪 K B L) (hx : bcT (C i) L x ∈ (d i).line L) :
    ∃ n : ℕ, (f i ^ n) • x ∈ glueLine π B C d L := by
  classical
  have h : ∀ j, ∃ n : ℕ, bcT (C j) L ((f i ^ n) • x) ∈ (d j).line L := fun j =>
    exists_pow_smul_bcT_mem π (f i) (f j) (ρ₁ i j) (ρ₂ i j) (d i) (d j) (hd i j) L x hx
  choose n hn using h
  refine ⟨Finset.univ.sup n, mem_glueLine π |>.mpr fun j => ?_⟩
  have hle : n j ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ j)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, bcT_smul']
  exact ((d j).line L).smul_mem _ (hn j)

theorem localized'_glueLine
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j))
    (L : FullLattice 𝒪 K) (i : Fin k) :
    (glueLine π B C d L).localized' (C i) (Submonoid.powers (f i)) (bcT (C i) L) = (d i).line L := by
  apply le_antisymm
  · rw [Submodule.localized'_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_glueLine π).mp hx i
  · intro y hy
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (bcT (C i) L) y
    have hx : bcT (C i) L x ∈ (d i).line L := by
      rw [← hxs]
      exact ((d i).line L).smul_of_tower_mem (s : B) hy
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_glueLine π (f := f) hd L i x hx
    rw [Submodule.mem_localized']
    refine ⟨(f i ^ n) • x, hn, ⟨f i ^ n, n, rfl⟩ * s, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff, LinearMap.map_smul, ← hxs, Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul,
      mul_smul]

include f in

theorem map_line_glue_eq
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j))
    (L : FullLattice 𝒪 K) (i : Fin k) :
    lineBaseChange (IsScalarTower.toAlgHom 𝒪 B (C i)) L (glueLine π B C d L) = (d i).line L := by
  rw [lineBaseChange_eq_localized' (Submonoid.powers (f i)), localized'_glueLine π (f := f) hd L i]

theorem invertible_quotient_glueLine (hf : Ideal.span (Set.range f) = ⊤)
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j))
    (L : FullLattice 𝒪 K) :
    Module.Invertible B (latticeBaseChange 𝒪 K B L ⧸ glueLine π B C d L) :=
  invertible_of_cover f hf C
    (fun i => latticeBaseChange 𝒪 K (C i) L ⧸ (glueLine π B C d L).localized' (C i) (Submonoid.powers (f i)) (bcT (C i) L))
    (fun i => (glueLine π B C d L).toLocalizedQuotient' (C i) (Submonoid.powers (f i)) (bcT (C i) L))
    (fun i => by
      haveI := (d i).invertible L
      exact Module.Invertible.congr (Submodule.quotEquivOfEq _ _ (localized'_glueLine π (f := f) hd L i).symm))

def glue (hf : Ideal.span (Set.range f) = ⊤)
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j)) :
    DeligneDatum (K := K) π B where
  line L := glueLine π B C d L
  invertible L := invertible_quotient_glueLine π hf hd L
  mono {M' M} h := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_glueLine π] at hx
    rw [mem_glueLine π]
    intro i
    rw [bcT_inclBaseChange]
    exact (d i).mono h (Submodule.mem_map_of_mem (hx i))
  homothety c M := by
    ext x
    rw [mem_glueLine π, Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨(actBaseChange B (scalarGL c) M).symm x, ?_, LinearEquiv.apply_symm_apply _ _⟩
      rw [mem_glueLine π]
      intro i
      have hi := hx i
      rw [(d i).homothety c M, Submodule.mem_map] at hi
      obtain ⟨y, hy, hyx⟩ := hi
      have : y = bcT (C i) M ((actBaseChange B (scalarGL c) M).symm x) := by
        apply (actBaseChange (C i) (scalarGL c) M).injective
        rw [LinearEquiv.coe_coe] at hyx
        rw [hyx, ← bcT_actBaseChange, LinearEquiv.apply_symm_apply]
      rw [← this]; exact hy
    · rintro ⟨y, hy, rfl⟩
      rw [mem_glueLine π] at hy
      intro i
      rw [(d i).homothety c M, LinearEquiv.coe_coe, bcT_actBaseChange]
      exact Submodule.mem_map_of_mem (hy i)
  nondeg 𝔭 h𝔭 := by
    haveI := h𝔭

    have hex : ∃ i, f i ∉ 𝔭 := by
      by_contra hcon
      push Not at hcon
      have hle : Ideal.span (Set.range f) ≤ 𝔭 := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
      rw [hf] at hle
      exact h𝔭.ne_top (top_le_iff.mp hle)
    obtain ⟨i, hi⟩ := hex
    have hdisj : Disjoint (Submonoid.powers (f i) : Set B) (𝔭 : Set B) := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ hn
      exact hi (h𝔭.mem_of_pow_mem n hn)

    set 𝔮 : Ideal (C i) := Ideal.map (algebraMap B (C i)) 𝔭 with h𝔮def
    haveI h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (f i)) (C i) 𝔭 h𝔭 hdisj
    have hle𝔮 : 𝔭 ≤ 𝔮.comap (algebraMap B (C i)) := Ideal.le_comap_map
    obtain ⟨M', M, hMM, hπM, h1, h2⟩ := (d i).nondeg 𝔮 h𝔮
    refine ⟨M', M, hMM, hπM, fun v hv hmem => h1 v hv ?_, fun v' hv' hmem => h2 v' hv' ?_⟩
    · obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      have key : bcT (C i) M ((1 : B) ⊗ₜ[𝒪] v) = (1 : C i) ⊗ₜ[𝒪] v := by rw [bcT_tmul, map_one]
      rw [← key, ← hyz, LinearMap.map_add]
      exact Submodule.mem_sup.mpr ⟨_, (mem_glueLine π).mp hy i, _, bcT_mem_smul_top M 𝔭 𝔮 hle𝔮 hz, rfl⟩
    · obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      have key : bcT (C i) M' ((1 : B) ⊗ₜ[𝒪] v') = (1 : C i) ⊗ₜ[𝒪] v' := by rw [bcT_tmul, map_one]
      rw [← key, ← hyz, LinearMap.map_add]
      exact Submodule.mem_sup.mpr ⟨_, (mem_glueLine π).mp hy i, _, bcT_mem_smul_top M' 𝔭 𝔮 hle𝔮 hz, rfl⟩

theorem map_glue (hf : Ideal.span (Set.range f) = ⊤)
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j))
    (i : Fin k) :
    (Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (C i)) (glue π hf hd) = d i := by
  apply DeligneDatum.ext'
  funext L
  exact map_line_glue_eq π (f := f) hd L i

theorem eq_of_forall_map_eq (hf : Ideal.span (Set.range f) = ⊤) (d₀ d₀' : DeligneDatum (K := K) π B)
    (h : ∀ i, (Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (C i)) d₀ =
      (Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (C i)) d₀') :
    d₀ = d₀' := by
  have hloc : ∀ i L, (d₀.line L).localized' (C i) (Submonoid.powers (f i)) (bcT (C i) L) =
      (d₀'.line L).localized' (C i) (Submonoid.powers (f i)) (bcT (C i) L) := fun i L => by
    rw [← map_line_eq_localized' π, ← map_line_eq_localized' π, h i]
  have hle : ∀ (N N' : ∀ L : FullLattice 𝒪 K, Submodule B (latticeBaseChange 𝒪 K B L)),
      (∀ i L, (N L).localized' (C i) (Submonoid.powers (f i)) (bcT (C i) L) =
        (N' L).localized' (C i) (Submonoid.powers (f i)) (bcT (C i) L)) → ∀ L, N L ≤ N' L := by
    intro N N' hNN' L x hx
    apply mem_of_forall_pow_smul_mem f hf (N' L) x
    intro i
    have hx' : bcT (C i) L x ∈ (N' L).localized' (C i) (Submonoid.powers (f i)) (bcT (C i) L) := by
      rw [← hNN' i L]
      exact bcT_mem_localized'_of_mem (Submonoid.powers (f i)) L (N L) hx
    obtain ⟨⟨_, n, rfl⟩, hs⟩ := (bcT_mem_localized'_iff (Submonoid.powers (f i)) L (N' L) x).mp hx'
    exact ⟨n, hs⟩
  apply DeligneDatum.ext'
  funext L
  exact le_antisymm (hle _ _ hloc L) (hle _ _ (fun i L => (hloc i L).symm) L)

end Glue

end P2mKcOmegaGlue

end

open P2mKcOmegaGlue in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B]
    {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (C : Fin k → Type) [∀ i, CommRing (C i)] [∀ i, Algebra 𝒪 (C i)] [∀ i, Algebra B (C i)]
    [∀ i, IsScalarTower 𝒪 B (C i)] [∀ i, IsLocalization.Away (f i) (C i)]
    (C₂ : Fin k → Fin k → Type) [∀ i j, CommRing (C₂ i j)] [∀ i j, Algebra 𝒪 (C₂ i j)] [∀ i j, Algebra B (C₂ i j)]
    [∀ i j, IsScalarTower 𝒪 B (C₂ i j)] [∀ i j, IsLocalization.Away (f i * f j) (C₂ i j)]
    (ρ₁ : ∀ i j, C i →ₐ[B] C₂ i j) (ρ₂ : ∀ i j, C j →ₐ[B] C₂ i j)
    (d : ∀ i, (Omega K π).obj (C i))
    (hd : ∀ i j, (Omega K π).map ((ρ₁ i j).restrictScalars 𝒪) (d i) = (Omega K π).map ((ρ₂ i j).restrictScalars 𝒪) (d j)) :
    ∃! d₀ : (Omega K π).obj B, ∀ i, (Omega K π).map (IsScalarTower.toAlgHom 𝒪 B (C i)) d₀ = d i := by
  refine ⟨glue π hf hd, fun i => map_glue π hf hd i, fun d₀' hd₀' => ?_⟩
  exact eq_of_forall_map_eq π (C := C) hf d₀' (glue π hf hd) fun i => by rw [hd₀' i, map_glue π hf hd i]

end S_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top (solution)
