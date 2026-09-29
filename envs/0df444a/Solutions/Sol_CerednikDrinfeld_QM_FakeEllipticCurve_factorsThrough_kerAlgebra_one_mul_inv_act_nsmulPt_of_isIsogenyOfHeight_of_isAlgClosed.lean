-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c681c812-928c-5b93-bfe0-5c9853ba9b1a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped Quaternion TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace KSGdd

open MvPowerSeries in
theorem constantCoeff_subst_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {R : Type} [CommRing R]
    {a : σ → MvPowerSeries τ R} (ha' : ∀ i, (a i).constantCoeff = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (subst a f) = MvPowerSeries.constantCoeff f := by
  have ha := hasSubst_of_constantCoeff_zero ha'
  rw [constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    have : constantCoeff (d.prod fun s e ↦ a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i : σ, d i ≠ 0 := by
        by_contra! hc
        exact hd <| Finsupp.ext hc
      simp [map_finsuppProd, ha']
      exact Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [zero_pow hi])
    rw [this, smul_zero]

theorem nilEval_zero_tuple {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ] {B' : Type} [CommRing B']
    [Algebra B B'] (n : ℕ) (φ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n φ (fun _ => (0 : B')) = algebraMap B B' (MvPowerSeries.constantCoeff φ) := by
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.aeval_def, ← MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂Hom_zero'_apply]
  congr 1
  rw [show (MvPolynomial.constantCoeff : MvPolynomial σ B → B) = MvPolynomial.coeff 0 from MvPolynomial.constantCoeff_eq,
    MvPowerSeries.coeff_trunc', if_pos (Finsupp.le_def.mpr fun _ => Nat.zero_le _), MvPowerSeries.coeff_zero_eq_constantCoeff]

theorem nilEval_X {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ] {B' : Type} [CommRing B']
    [Algebra B B'] (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (s : σ → B') (hs : ∀ i, s i ∈ J) (i : σ) :
    MvFormalGroup.nilEval n (MvPowerSeries.X i : MvPowerSeries σ B) s = s i := by
  classical
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.X_def, MvPowerSeries.trunc']
  by_cases hn : n = 0
  · subst hn
    have hs0 : s i = 0 := by
      have := Ideal.pow_mem_pow (hs i) 1
      rwa [hJ, Ideal.mem_bot, pow_one] at this
    rw [MvPowerSeries.truncFinset_monomial_eq_zero, map_zero, hs0]
    simp [Finsupp.single_le_iff]
  · rw [MvPowerSeries.truncFinset_monomial, ← MvPolynomial.X, MvPolynomial.aeval_X]
    simp only [Finset.mem_Iic, Finsupp.single_le_iff]
    show 1 ≤ (Finsupp.equivFunOnFinite.symm fun _ : σ => n) i
    simp; omega

theorem algHom_nilEval {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ] {B' B'' : Type} [CommRing B']
    [CommRing B''] [Algebra B B'] [Algebra B B''] (φ : B' →ₐ[B] B'') (n : ℕ) (ψ : MvPowerSeries σ B) (s : σ → B') :
    φ (MvFormalGroup.nilEval n ψ s) = MvFormalGroup.nilEval n ψ (φ ∘ s) := by
  unfold MvFormalGroup.nilEval
  have := MvPolynomial.comp_aeval (f := s) φ
  exact (congrFun (congrArg DFunLike.coe this) _).trans rfl

section group

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
  {F : MvFormalGroup 2 B} {θ : RelativeGroupLaw.FormalCoordinates f 2}

theorem theta_zero (hθ : L.IsFormalCoordinates F θ) (B' : Type) [CommRing B'] [Algebra B B'] :
    θ B' (fun _ => 0) = L.one (Scheme.specOver (𝒪 := B) B') := by
  have h := (hθ.2 B' ⊥ 0 (by simp)).2.2.2 (fun _ => 0) (fun _ => 0) (fun _ => Submodule.zero_mem _)
    (fun _ => Submodule.zero_mem _)
  have h0 : F.nilMul 0 (fun _ => (0 : B')) (fun _ => 0) = fun _ => 0 := by
    funext i
    show MvFormalGroup.nilEval 0 (F.toPowerSeries i) (Sum.elim (fun _ => (0 : B')) fun _ => 0) = 0
    rw [show (Sum.elim (fun _ => (0 : B')) fun _ => (0 : B')) = fun _ => 0 from funext fun x => by cases x <;> rfl,
      nilEval_zero_tuple, F.constantCoeff_eq_zero, map_zero]
  rw [h0] at h
  letI := L.pointGroup (Scheme.specOver (𝒪 := B) B')
  have h' : θ B' (fun _ => 0) * 1 = θ B' (fun _ => 0) * θ B' (fun _ => 0) := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

theorem nsmulPt_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (t' : T' ⟶ Spec (CommRingCat.of B))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n x) x) = L.mul t' (nsmulPt L t' n _) _
    rw [L.mul_natural, ih]

theorem nsmulPt_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n x = x ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => exact (pow_zero x).symm
  | succ n ih =>
    show L.mul t (nsmulPt L t n x) x = x ^ (n + 1)
    rw [ih, pow_succ]; rfl

theorem nsmulPt_theta (hθ : L.IsFormalCoordinates F θ) (B' : Type) [CommRing B'] [Algebra B B']
    (J : Ideal B') (M : ℕ) (hJ : J ^ (M + 1) = ⊥) (s : Fin 2 → B') (hs : ∀ i, s i ∈ J) (n : ℕ) :
    nsmulPt L (Scheme.specOver (𝒪 := B) B') n (θ B' s) =
      θ B' (fun i => MvFormalGroup.nilEval M (F.nthSeries n i) s) := by
  classical
  induction n with
  | zero =>
    show L.one _ = _
    rw [MvFormalGroup.nthSeries_zero]
    have : (fun i : Fin 2 => MvFormalGroup.nilEval M (0 : MvPowerSeries (Fin 2) B) s) = fun _ => (0 : B') := by
      funext i; unfold MvFormalGroup.nilEval; rw [map_zero, map_zero]
    rw [this, theta_zero L hθ]
  | succ n ih =>
    show L.mul _ (nsmulPt L _ n (θ B' s)) (θ B' s) = _
    rw [ih]
    have hcc : ∀ l, MvPowerSeries.constantCoeff (Sum.elim (F.nthSeries n) (fun j => MvPowerSeries.X j) l) = 0 := by
      rintro (l | l)
      · exact MvFormalGroup.constantCoeff_nthSeries F n l
      · exact MvPowerSeries.constantCoeff_X l
    have key := MvFormalGroup.nilEval_subst_of_mem J M hJ s hs (Sum.elim (F.nthSeries n) fun j => MvPowerSeries.X j) hcc
    have htJ : ∀ i, MvFormalGroup.nilEval M (F.nthSeries n i) s ∈ J := fun i => (key 0).1 (Sum.inl i)
    have e : (fun i => MvFormalGroup.nilEval M (F.nthSeries (n + 1) i) s) =
        F.nilMul M (fun i => MvFormalGroup.nilEval M (F.nthSeries n i) s) s := by
      funext i
      rw [MvFormalGroup.nthSeries_succ]
      show MvFormalGroup.nilEval M (MvPowerSeries.subst (Sum.elim (F.nthSeries n) fun j => MvPowerSeries.X j) (F.toPowerSeries i)) s
        = MvFormalGroup.nilEval M (F.toPowerSeries i) (Sum.elim (fun i => MvFormalGroup.nilEval M (F.nthSeries n i) s) s)
      rw [(key (F.toPowerSeries i)).2]
      congr 1
      funext l
      rcases l with l | l
      · rfl
      · exact nilEval_X J M hJ s hs l
    rw [e]
    exact ((hθ.2 B' J M hJ).2.2.2 _ _ htJ hs).symm

end group

end KSGdd

open KSGdd in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))
    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)
    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (A.L.one t)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 P → FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 Q →
        FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (A.L.mul t P Q) ∧ FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (A.L.inv t P)) ∧
    (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 P → FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (pushPt (A.act x) (A.act_over x) P)) ∧
    (∃ c : ℕ, ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 P → nsmulPt A.L t (r ^ c) P = A.L.one t) := by
  classical

  have hγc : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := hγ.1.constantCoeff
  obtain ⟨hnat, hcoords⟩ := hA.1
  have DICT := CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_kerAlgebra_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
    coord hcoord k hkr A XA θA hA Y γ h hγ

  set R : Type := FormalODModule.KerAlgebra γ with hR
  set Xb : Fin 2 → FormalODModule.KerAlgebra γ := fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i) with hXb
  set Pu := θA (FormalODModule.KerAlgebra γ) Xb with hPu

  have hnt : Nontrivial (FormalODModule.KerAlgebra γ) := by
    have h1 := hγ.2.2.2 k (RingHom.id k)
    rw [CerednikDrinfeld.SpecialFormal.Series.map_ringHom_id] at h1
    apply Module.nontrivial_of_finrank_pos (R := k)
    rw [h1]; exact pow_pos (Fact.out : r.Prime).pos h
  have hIle : ∀ a ∈ Ideal.span (Set.range γ), MvPowerSeries.constantCoeff a = 0 := by
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨j, rfl⟩; exact hγc j
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  let ev0 : FormalODModule.KerAlgebra γ →+* k :=
    Ideal.Quotient.lift (Ideal.span (Set.range γ)) (MvPowerSeries.constantCoeff) hIle
  have hev0 : ev0.comp (algebraMap k (FormalODModule.KerAlgebra γ)) = RingHom.id k := by
    refine RingHom.ext fun x => ?_
    change MvPowerSeries.constantCoeff (algebraMap k (MvPowerSeries (Fin 2) k) x) = x
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.constantCoeff_C]
  have hXnil : ∀ i, IsNilpotent (Xb i) := by
    intro i
    haveI := hγ.2.1
    haveI := hnt
    haveI : IsLocalRing (FormalODModule.KerAlgebra γ) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span (Set.range γ))) Ideal.Quotient.mk_surjective
    haveI : IsArtinianRing (FormalODModule.KerAlgebra γ) := IsArtinianRing.of_finite k _
    have hmem : Xb i ∈ IsLocalRing.maximalIdeal (FormalODModule.KerAlgebra γ) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map ev0
      rw [hXb, Ideal.Quotient.lift_mk, MvPowerSeries.constantCoeff_X] at this
      exact not_isUnit_zero this
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := FormalODModule.KerAlgebra γ)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.zero_eq_bot] at hN
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow hmem N
    rwa [hN, Ideal.mem_bot] at this

  let 𝔪 : Ideal (FormalODModule.KerAlgebra γ) := Ideal.span (Set.range Xb)
  have h𝔪nil : IsNilpotent 𝔪 := by
    apply (Ideal.FG.isNilpotent_iff_le_nilradical ⟨Finset.univ.image Xb, by simp [𝔪]⟩).mpr
    rw [Ideal.span_le]; rintro x ⟨i, rfl⟩; exact hXnil i
  obtain ⟨M₀, hM₀⟩ := h𝔪nil
  have h𝔪M : ∀ M, M₀ ≤ M → 𝔪 ^ (M + 1) = ⊥ := by
    intro M hM
    rw [Ideal.zero_eq_bot] at hM₀
    exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hM₀.le)
  have hXb𝔪 : ∀ i, Xb i ∈ 𝔪 := fun i => Ideal.subset_span ⟨i, rfl⟩

  have hγX : ∀ M, M₀ ≤ M → ∀ i, MvFormalGroup.nilEval M (γ i) Xb = 0 := by
    intro M hM
    exact (DICT (FormalODModule.KerAlgebra γ) 𝔪 M (h𝔪M M hM) Xb hXb𝔪).mp ⟨𝟙 _, Category.id_comp _⟩

  have descend : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f)
      (P₀ : T ⟶ Spec (CommRingCat.of (FormalODModule.KerAlgebra γ))), P₀ ≫ Pu.1 = P.1 →
      ∃ hP₀ : P₀ ≫ Scheme.specOver (𝒪 := k) (FormalODModule.KerAlgebra γ) = t, P = schemeHomOverComp P₀ hP₀ Pu := by
    intro T t P P₀ hP₀
    have hb : P₀ ≫ Scheme.specOver (𝒪 := k) (FormalODModule.KerAlgebra γ) = t := by
      rw [← Pu.2, ← Category.assoc, hP₀, P.2]
    exact ⟨hb, Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hP₀])⟩

  have torsion_univ : ∃ c : ℕ, nsmulPt A.L (Scheme.specOver (𝒪 := k) (FormalODModule.KerAlgebra γ)) (r ^ c) Pu = A.L.one _ := by
    obtain ⟨N, β, hβ, hβγ⟩ :=
      CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field r hkr XA Y γ h hγ
    refine ⟨N, ?_⟩
    rw [hPu, nsmulPt_theta A.L hA.1 (FormalODModule.KerAlgebra γ) 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 (r ^ N)]
    have e : (fun i => MvFormalGroup.nilEval M₀ (XA.F.nthSeries (r ^ N) i) Xb) = fun _ => (0 : FormalODModule.KerAlgebra γ) := by
      funext i
      rw [← FormalODModule.act_natCast, Nat.cast_pow, ← hβγ]
      show MvFormalGroup.nilEval M₀ (MvPowerSeries.subst γ (β i)) Xb = 0
      rw [(MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 γ hγc (β i)).2,
        show (fun j => MvFormalGroup.nilEval M₀ (γ j) Xb) = fun _ => (0 : FormalODModule.KerAlgebra γ) from
          funext (hγX M₀ le_rfl),
        nilEval_zero_tuple, hβ.constantCoeff, map_zero]
    rw [e, theta_zero A.L hA.1]
  obtain ⟨c, hc⟩ := torsion_univ

  have one_univ : FactorsThrough Pu.1 (A.L.one (Scheme.specOver (𝒪 := k) (FormalODModule.KerAlgebra γ))) := by
    rw [← hc]

    rw [hPu, nsmulPt_theta A.L hA.1 (FormalODModule.KerAlgebra γ) 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 (r ^ c)]
    refine (DICT (FormalODModule.KerAlgebra γ) 𝔪 M₀ (h𝔪M M₀ le_rfl) _ ?_).mpr ?_
    · intro i
      exact (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 (XA.F.nthSeries (r ^ c))
        (MvFormalGroup.constantCoeff_nthSeries _ _) (MvPowerSeries.X 0)).1 i
    · intro i
      rw [← (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 (XA.F.nthSeries (r ^ c))
        (MvFormalGroup.constantCoeff_nthSeries _ _) (γ i)).2]

      have hcomm : MvPowerSeries.subst (XA.F.nthSeries (r ^ c)) (γ i) = MvPowerSeries.subst γ (Y.F.nthSeries (r ^ c) i) := by
        have h1 := hγ.1.2.1 ((r : Zp2 r) ^ c)
        rw [← Nat.cast_pow, FormalODModule.act_natCast, FormalODModule.act_natCast] at h1
        exact congrFun h1 i
      rw [hcomm, (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 γ hγc _).2,
        show (fun j => MvFormalGroup.nilEval M₀ (γ j) Xb) = fun _ => (0 : FormalODModule.KerAlgebra γ) from
          funext (hγX M₀ le_rfl),
        nilEval_zero_tuple, MvFormalGroup.constantCoeff_nthSeries, map_zero]

  have act_univ : ∀ x : ↥Λ, FactorsThrough Pu.1 (pushPt (A.act x) (A.act_over x) Pu) := by
    intro x
    have hact := hA.2 (FormalODModule.KerAlgebra γ) 𝔪 M₀ (h𝔪M M₀ le_rfl) x Xb hXb𝔪
    rw [hPu, ← hact]

    obtain ⟨⟨-, hlaw⟩, hactc, hvarpi⟩ := hγ.1
    have ha : γ.comp (XA.act (coord x).1) = (Y.act (coord x).1).comp γ := hactc _
    have hb : γ.comp ((XA.act (coord x).2).comp XA.varpi) = ((Y.act (coord x).2).comp Y.varpi).comp γ := by
      rw [← CerednikDrinfeld.SpecialFormal.Series.comp_assoc _ _ _ (XA.isLawHom_act _).1 XA.isLawHom_varpi.1, hactc,
        CerednikDrinfeld.SpecialFormal.Series.comp_assoc _ _ _ hγc XA.isLawHom_varpi.1, hvarpi,
        ← CerednikDrinfeld.SpecialFormal.Series.comp_assoc _ _ _ Y.isLawHom_varpi.1 hγc]
    have haC : ∀ l, MvPowerSeries.constantCoeff (XA.act (coord x).1 l) = 0 := (XA.isLawHom_act _).1
    have hbC : ∀ l, MvPowerSeries.constantCoeff (((XA.act (coord x).2).comp XA.varpi) l) = 0 :=
      CerednikDrinfeld.SpecialFormal.Series.constantCoeff_comp (XA.isLawHom_act _).1 XA.isLawHom_varpi.1
    have habC : ∀ l, MvPowerSeries.constantCoeff (Sum.elim (XA.act (coord x).1) ((XA.act (coord x).2).comp XA.varpi) l) = 0 := by
      rintro (l | l)
      · exact haC l
      · exact hbC l

    obtain ⟨pt, hpt⟩ : ∃ pt : Fin 2 ⊕ Fin 2 → FormalODModule.KerAlgebra γ,
      pt = fun l => MvFormalGroup.nilEval M₀ (Sum.elim (XA.act (coord x).1) ((XA.act (coord x).2).comp XA.varpi) l) Xb := ⟨_, rfl⟩
    have hpt𝔪 : ∀ l, pt l ∈ 𝔪 := hpt ▸ (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 _ habC 0).1
    have hΦ'c : ∀ l, MvPowerSeries.constantCoeff (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) l) = 0 := by
      rintro (j | j)
      · show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ (γ j)) = 0
        rw [constantCoeff_subst_of_constantCoeff_eq_zero (fun l => MvPowerSeries.constantCoeff_X _), hγc]
      · show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ (γ j)) = 0
        rw [constantCoeff_subst_of_constantCoeff_eq_zero (fun l => MvPowerSeries.constantCoeff_X _), hγc]
    have hγzero : (fun j => MvFormalGroup.nilEval M₀ (γ j) Xb) = fun _ => (0 : FormalODModule.KerAlgebra γ) :=
      funext (hγX M₀ le_rfl)
    have hγa : ∀ j, MvFormalGroup.nilEval M₀ (γ j) (fun l => pt (Sum.inl l)) = 0 := by
      intro j
      rw [hpt]
      show MvFormalGroup.nilEval M₀ (γ j) (fun l => MvFormalGroup.nilEval M₀ (XA.act (coord x).1 l) Xb) = 0
      rw [← (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 _ haC (γ j)).2,
        show MvPowerSeries.subst (XA.act (coord x).1) (γ j) = (γ.comp (XA.act (coord x).1)) j from rfl, ha,
        show ((Y.act (coord x).1).comp γ) j = MvPowerSeries.subst γ (Y.act (coord x).1 j) from rfl,
        (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 γ hγc _).2, hγzero, nilEval_zero_tuple,
        (Y.isLawHom_act _).1, map_zero]
    have hγb : ∀ j, MvFormalGroup.nilEval M₀ (γ j) (fun l => pt (Sum.inr l)) = 0 := by
      intro j
      rw [hpt]
      show MvFormalGroup.nilEval M₀ (γ j) (fun l => MvFormalGroup.nilEval M₀ (((XA.act (coord x).2).comp XA.varpi) l) Xb) = 0
      rw [← (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 _ hbC (γ j)).2,
        show MvPowerSeries.subst ((XA.act (coord x).2).comp XA.varpi) (γ j) = (γ.comp ((XA.act (coord x).2).comp XA.varpi)) j from rfl,
        hb, show ((((Y.act (coord x).2).comp Y.varpi)).comp γ) j = MvPowerSeries.subst γ (((Y.act (coord x).2).comp Y.varpi) j) from rfl,
        (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 γ hγc _).2, hγzero, nilEval_zero_tuple,
        CerednikDrinfeld.SpecialFormal.Series.constantCoeff_comp (Y.isLawHom_act _).1 Y.isLawHom_varpi.1, map_zero]
    have e1 : (fun i => MvFormalGroup.nilEval M₀
        (Series.addVia XA.F (XA.act (coord x).1) ((XA.act (coord x).2).comp XA.varpi) i) Xb) =
        fun j => MvFormalGroup.nilEval M₀ (XA.F.toPowerSeries j) pt := by
      funext j
      show MvFormalGroup.nilEval M₀ (MvPowerSeries.subst
        (Sum.elim (XA.act (coord x).1) ((XA.act (coord x).2).comp XA.varpi)) (XA.F.toPowerSeries j)) Xb = _
      rw [(MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) Xb hXb𝔪 _ habC _).2, hpt]
    rw [e1]
    refine (DICT (FormalODModule.KerAlgebra γ) 𝔪 M₀ (h𝔪M M₀ le_rfl) _ ?_).mpr ?_
    · exact (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) _ hpt𝔪 XA.F.toPowerSeries
        XA.F.constantCoeff_eq_zero 0).1
    · intro i
      rw [← (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) pt hpt𝔪 XA.F.toPowerSeries
        XA.F.constantCoeff_eq_zero (γ i)).2, hlaw i,
        (MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) pt hpt𝔪 _ hΦ'c (Y.F.toPowerSeries i)).2]
      have inner : (fun l => MvFormalGroup.nilEval M₀ (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) l) pt) =
          fun _ => (0 : FormalODModule.KerAlgebra γ) := by
        funext l
        rcases l with j | j
        · show MvFormalGroup.nilEval M₀ (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) pt = 0
          rw [(MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) pt hpt𝔪 _ (fun l => MvPowerSeries.constantCoeff_X _) (γ j)).2]
          have : (fun l => MvFormalGroup.nilEval M₀ (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) pt) =
              fun l => pt (Sum.inl l) := funext fun l => nilEval_X 𝔪 M₀ (h𝔪M M₀ le_rfl) pt hpt𝔪 _
          rw [this]; exact hγa j
        · show MvFormalGroup.nilEval M₀ (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) pt = 0
          rw [(MvFormalGroup.nilEval_subst_of_mem 𝔪 M₀ (h𝔪M M₀ le_rfl) pt hpt𝔪 _ (fun l => MvPowerSeries.constantCoeff_X _) (γ j)).2]
          have : (fun l => MvFormalGroup.nilEval M₀ (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) pt) =
              fun l => pt (Sum.inr l) := funext fun l => nilEval_X 𝔪 M₀ (h𝔪M M₀ le_rfl) pt hpt𝔪 _
          rw [this]; exact hγb j
      rw [inner, nilEval_zero_tuple, Y.F.constantCoeff_eq_zero, map_zero]

  have pair_univ : ∀ (B'' : Type) [CommRing B''] [Algebra k B'']
      (iL iR : FormalODModule.KerAlgebra γ →ₐ[k] B''),
      FactorsThrough Pu.1 (A.L.mul (Scheme.specOver (𝒪 := k) B'')
        (schemeHomOverComp (Spec.map (CommRingCat.ofHom iL.toRingHom)) (Scheme.specMap_algHom_comp_specOver iL) Pu)
        (schemeHomOverComp (Spec.map (CommRingCat.ofHom iR.toRingHom)) (Scheme.specMap_algHom_comp_specOver iR) Pu)) := by
    intro B'' _ _ iL iR
    obtain ⟨x1, hx1⟩ : ∃ x1 : Fin 2 → B'', x1 = (iL : _ → B'') ∘ Xb := ⟨_, rfl⟩
    obtain ⟨x2, hx2⟩ : ∃ x2 : Fin 2 → B'', x2 = (iR : _ → B'') ∘ Xb := ⟨_, rfl⟩
    have hx1n : ∀ i, IsNilpotent (x1 i) := fun i => by rw [hx1]; exact (hXnil i).map iL.toRingHom
    have hx2n : ∀ i, IsNilpotent (x2 i) := fun i => by rw [hx2]; exact (hXnil i).map iR.toRingHom
    obtain ⟨J₂, hJ₂def⟩ : ∃ J₂ : Ideal B'', J₂ = Ideal.span (Set.range x1 ∪ Set.range x2) := ⟨_, rfl⟩
    have hJ₂nil : IsNilpotent J₂ := by
      rw [hJ₂def]
      apply (Ideal.FG.isNilpotent_iff_le_nilradical ⟨Finset.univ.image x1 ∪ Finset.univ.image x2, by simp⟩).mpr
      rw [Ideal.span_le]
      rintro y (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact hx1n i
      · exact hx2n i
    obtain ⟨M₁, hM₁⟩ := hJ₂nil
    have hJ₂M : J₂ ^ (M₀ + M₁ + 1) = ⊥ := by
      rw [Ideal.zero_eq_bot] at hM₁
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hM₁.le)
    have hx1J : ∀ i, x1 i ∈ J₂ := fun i => by rw [hJ₂def]; exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)
    have hx2J : ∀ i, x2 i ∈ J₂ := fun i => by rw [hJ₂def]; exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)
    have hx12 : ∀ l, Sum.elim x1 x2 l ∈ J₂ := by
      rintro (l | l)
      · exact hx1J l
      · exact hx2J l

    have hP1 := hnat (FormalODModule.KerAlgebra γ) B'' iL Xb hXnil
    have hP2 := hnat (FormalODModule.KerAlgebra γ) B'' iR Xb hXnil
    rw [← hPu, ← hx1] at hP1
    rw [← hPu, ← hx2] at hP2
    rw [← hP1, ← hP2]

    have hmul := (hcoords B'' J₂ (M₀ + M₁) hJ₂M).2.2.2 x1 x2 hx1J hx2J
    have hwJ : ∀ i, XA.F.nilMul (M₀ + M₁) x1 x2 i ∈ J₂ :=
      (MvFormalGroup.nilEval_subst_of_mem J₂ (M₀ + M₁) hJ₂M (Sum.elim x1 x2) hx12 XA.F.toPowerSeries
        XA.F.constantCoeff_eq_zero 0).1
    obtain ⟨⟨-, hlaw⟩, -, -⟩ := hγ.1
    have hΦ'c : ∀ l, MvPowerSeries.constantCoeff (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) l) = 0 := by
      rintro (j | j)
      · show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ (γ j)) = 0
        rw [constantCoeff_subst_of_constantCoeff_eq_zero (fun l => MvPowerSeries.constantCoeff_X _), hγc]
      · show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ (γ j)) = 0
        rw [constantCoeff_subst_of_constantCoeff_eq_zero (fun l => MvPowerSeries.constantCoeff_X _), hγc]
    have hγX' : ∀ j, MvFormalGroup.nilEval (M₀ + M₁) (γ j) Xb = 0 := hγX _ (by omega)
    have hγw : ∀ i, MvFormalGroup.nilEval (M₀ + M₁) (γ i) (XA.F.nilMul (M₀ + M₁) x1 x2) = 0 := by
      intro i
      show MvFormalGroup.nilEval (M₀ + M₁) (γ i) (fun j => MvFormalGroup.nilEval (M₀ + M₁) (XA.F.toPowerSeries j) (Sum.elim x1 x2)) = 0
      rw [← (MvFormalGroup.nilEval_subst_of_mem J₂ (M₀ + M₁) hJ₂M _ hx12 XA.F.toPowerSeries XA.F.constantCoeff_eq_zero (γ i)).2,
        hlaw i, (MvFormalGroup.nilEval_subst_of_mem J₂ (M₀ + M₁) hJ₂M _ hx12 _ hΦ'c (Y.F.toPowerSeries i)).2]
      have inner : (fun l => MvFormalGroup.nilEval (M₀ + M₁) (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) l)
          (Sum.elim x1 x2)) = fun _ => (0 : B'') := by
        funext l
        rcases l with j | j
        · show MvFormalGroup.nilEval (M₀ + M₁) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) (Sum.elim x1 x2) = 0
          rw [(MvFormalGroup.nilEval_subst_of_mem J₂ (M₀ + M₁) hJ₂M _ hx12 _ (fun l => MvPowerSeries.constantCoeff_X _) (γ j)).2]
          have : (fun l => MvFormalGroup.nilEval (M₀ + M₁) (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (Sum.elim x1 x2)) = x1 :=
            funext fun l => nilEval_X J₂ (M₀ + M₁) hJ₂M _ hx12 _
          rw [this, hx1, ← algHom_nilEval iL, hγX' j, map_zero]
        · show MvFormalGroup.nilEval (M₀ + M₁) (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (γ j)) (Sum.elim x1 x2) = 0
          rw [(MvFormalGroup.nilEval_subst_of_mem J₂ (M₀ + M₁) hJ₂M _ hx12 _ (fun l => MvPowerSeries.constantCoeff_X _) (γ j)).2]
          have : (fun l => MvFormalGroup.nilEval (M₀ + M₁) (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) (Sum.elim x1 x2)) = x2 :=
            funext fun l => nilEval_X J₂ (M₀ + M₁) hJ₂M _ hx12 _
          rw [this, hx2, ← algHom_nilEval iR, hγX' j, map_zero]
      rw [inner, nilEval_zero_tuple, Y.F.constantCoeff_eq_zero, map_zero]
    rw [← hmul]
    exact (DICT B'' J₂ (M₀ + M₁) hJ₂M _ hwJ).mpr hγw

  have mul_univ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
      FactorsThrough Pu.1 P → FactorsThrough Pu.1 Q → FactorsThrough Pu.1 (A.L.mul t P Q) := by
    intro T t P Q hP hQ
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨Q₀, hQ₀⟩ := hQ
    obtain ⟨hbP, rfl⟩ := descend t P P₀ hP₀
    obtain ⟨hbQ, rfl⟩ := descend t Q Q₀ hQ₀
    let iL : FormalODModule.KerAlgebra γ →ₐ[k] FormalODModule.KerAlgebra γ ⊗[k] FormalODModule.KerAlgebra γ :=
      { toRingHom := Algebra.TensorProduct.includeLeftRingHom, commutes' := fun c => rfl }
    let iR : FormalODModule.KerAlgebra γ →ₐ[k] FormalODModule.KerAlgebra γ ⊗[k] FormalODModule.KerAlgebra γ :=
      { toRingHom := (Algebra.TensorProduct.includeRight (R := k) (A := FormalODModule.KerAlgebra γ)
          (B := FormalODModule.KerAlgebra γ)).toRingHom,
        commutes' := fun c => (Algebra.TensorProduct.includeRight (R := k) (A := FormalODModule.KerAlgebra γ)
          (B := FormalODModule.KerAlgebra γ)).commutes c }

    let ψ' := pullback.lift P₀ Q₀ (hbP.trans hbQ.symm)
    let ψ := ψ' ≫ (pullbackSpecIso k (FormalODModule.KerAlgebra γ) (FormalODModule.KerAlgebra γ)).hom
    have hψ1 : ψ ≫ Spec.map (CommRingCat.ofHom iL.toRingHom) = P₀ := by
      show (ψ' ≫ _) ≫ _ = _
      rw [Category.assoc]
      erw [pullbackSpecIso_hom_fst]
      exact pullback.lift_fst _ _ _
    have hψ2 : ψ ≫ Spec.map (CommRingCat.ofHom iR.toRingHom) = Q₀ := by
      show (ψ' ≫ _) ≫ _ = _
      rw [Category.assoc]
      erw [pullbackSpecIso_hom_snd]
      exact pullback.lift_snd _ _ _
    have hψb : ψ ≫ Scheme.specOver (𝒪 := k) (FormalODModule.KerAlgebra γ ⊗[k] FormalODModule.KerAlgebra γ) = t := by
      show (ψ' ≫ _) ≫ Spec.map (CommRingCat.ofHom (algebraMap k _)) = _
      rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc, pullback.lift_fst]
      exact hbP
    have key : ∀ (X1 X2 : SchemeHomOver (Scheme.specOver (𝒪 := k) (FormalODModule.KerAlgebra γ ⊗[k] FormalODModule.KerAlgebra γ)) A.f),
        FactorsThrough Pu.1 (A.L.mul _ X1 X2) → ψ ≫ X1.1 = P₀ ≫ Pu.1 → ψ ≫ X2.1 = Q₀ ≫ Pu.1 →
        FactorsThrough Pu.1 (A.L.mul t (schemeHomOverComp P₀ hbP Pu) (schemeHomOverComp Q₀ hbQ Pu)) := by
      intro X1 X2 hX h1 h2
      obtain ⟨W₀, hW₀⟩ := hX
      have e1 : schemeHomOverComp P₀ hbP Pu = schemeHomOverComp ψ hψb X1 := Subtype.ext (by
        rw [GoodReductionJacobian.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, h1])
      have e2 : schemeHomOverComp Q₀ hbQ Pu = schemeHomOverComp ψ hψb X2 := Subtype.ext (by
        rw [GoodReductionJacobian.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, h2])
      rw [e1, e2, ← A.L.mul_natural]
      refine ⟨ψ ≫ W₀, ?_⟩
      rw [Category.assoc, hW₀, GoodReductionJacobian.schemeHomOverComp_coe]
    exact key _ _ (pair_univ (FormalODModule.KerAlgebra γ ⊗[k] FormalODModule.KerAlgebra γ) iL iR)
      (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, hψ1])
      (by rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, hψ2])

  have pow_fac : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough Pu.1 P → ∀ n : ℕ, FactorsThrough Pu.1 (nsmulPt A.L t n P) := by
    intro T t P hP n
    induction n with
    | zero =>
      obtain ⟨P₀, hP₀⟩ := hP
      obtain ⟨hb, -⟩ := descend t P P₀ hP₀
      obtain ⟨E₀, hE₀⟩ := one_univ
      refine ⟨P₀ ≫ E₀, ?_⟩
      show _ = (A.L.one t).1
      rw [← A.L.one_natural _ t P₀ hb, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, hE₀]
    | succ n ih => exact mul_univ t _ _ ih hP
  have tors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
      FactorsThrough Pu.1 P → nsmulPt A.L t (r ^ c) P = A.L.one t := by
    intro T t P hP
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨hb, rfl⟩ := descend t P P₀ hP₀
    rw [← nsmulPt_natural A.L _ t P₀ hb, hc, A.L.one_natural]
  refine ⟨fun {T} t => ?_, fun {T} t P Q hP hQ => ⟨mul_univ t P Q hP hQ, ?_⟩, fun x {T} t P hP => ?_, ⟨c, fun {T} t P hP => tors t P hP⟩⟩
  ·
    obtain ⟨E₀, hE₀⟩ := one_univ
    have hb : (t ≫ Spec.map (CommRingCat.ofHom ev0)) ≫ Scheme.specOver (𝒪 := k) (FormalODModule.KerAlgebra γ) = t := by
      rw [Scheme.specOver, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hev0, CommRingCat.ofHom_id,
        Spec.map_id, Category.comp_id]
    refine ⟨(t ≫ Spec.map (CommRingCat.ofHom ev0)) ≫ E₀, ?_⟩
    rw [← A.L.one_natural _ t _ hb, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, hE₀]
  ·
    letI := A.L.pointGroup t
    have hpow : P ^ (r ^ c) = 1 := by rw [← nsmulPt_eq_pow A.L t]; exact tors t P hP
    have hinv : A.L.inv t P = P ^ (r ^ c - 1) := by
      show P⁻¹ = P ^ (r ^ c - 1)
      have h1 : 1 ≤ r ^ c := Nat.one_le_pow _ _ (Fact.out : r.Prime).pos
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel h1, hpow]
    rw [hinv, ← nsmulPt_eq_pow A.L t]
    exact pow_fac t P hP _
  ·
    obtain ⟨P₀, hP₀⟩ := hP
    obtain ⟨hb, rfl⟩ := descend t P P₀ hP₀
    obtain ⟨W₀, hW₀⟩ := act_univ x
    refine ⟨P₀ ≫ W₀, ?_⟩
    rw [Category.assoc, hW₀]
    simp only [pushPt, mapPt_coe, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_one_mul_inv_act_nsmulPt_of_isIsogenyOfHeight_of_isAlgClosed (solution)
