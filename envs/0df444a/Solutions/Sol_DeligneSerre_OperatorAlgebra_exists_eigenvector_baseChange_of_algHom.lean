-- Prove2me | solution 1 for DeligneSerre.OperatorAlgebra.exists_eigenvector_baseChange_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/af35819e-2454-53d1-80e0-fd459f89541e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_OperatorAlgebra_exists_eigenvector_baseChange_of_algHom

set_option autoImplicit false

open scoped TensorProduct

namespace DeligneSerre
namespace OperatorAlgebra
namespace PointLemma

section Nilp

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

theorem pow_apply_mem (p : Submodule R E) (N : Module.End R E) (hmaps : ∀ x ∈ p, N x ∈ p)
    (x : E) (hx : x ∈ p) (j : ℕ) : (N ^ j) x ∈ p := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hmaps _ ih

theorem exists_ne_zero_mem_ker_of_isNilpotent (p : Submodule R E) (hp : p ≠ ⊥)
    (N : Module.End R E) (hN : IsNilpotent N) (hmaps : ∀ x ∈ p, N x ∈ p) :
    ∃ v ∈ p, v ≠ 0 ∧ N v = 0 := by
  classical
  obtain ⟨x, hxp, hx0⟩ := (Submodule.ne_bot_iff p).mp hp
  obtain ⟨k, hk⟩ := hN
  have hex : ∃ j : ℕ, (N ^ j) x = 0 := ⟨k, by rw [hk]; rfl⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀spec : (N ^ j₀) x = 0 := Nat.find_spec hex
  have hj₀pos : 0 < j₀ := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0, pow_zero, Module.End.one_apply] at hj₀spec
    exact hx0 hj₀spec
  refine ⟨(N ^ (j₀ - 1)) x, pow_apply_mem p N hmaps x hxp _, ?_, ?_⟩
  · intro h
    have := Nat.find_min hex (m := j₀ - 1) (by omega)
    exact this h
  · rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hj₀pos]
    exact hj₀spec

theorem exists_common_ker_finset {ι : Type*} (N : ι → Module.End R E)
    (hcomm : ∀ i j, Commute (N i) (N j)) (hnil : ∀ i, IsNilpotent (N i)) (s : Finset ι) :
    ∀ (p : Submodule R E), p ≠ ⊥ → (∀ i, ∀ x ∈ p, N i x ∈ p) →
      ∃ v ∈ p, v ≠ 0 ∧ ∀ i ∈ s, N i v = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro p hp _
    obtain ⟨x, hxp, hx0⟩ := (Submodule.ne_bot_iff p).mp hp
    exact ⟨x, hxp, hx0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i₀ s hi₀ ih =>
    intro p hp hmaps
    set p' : Submodule R E := p ⊓ LinearMap.ker (N i₀) with hp'
    have hp'ne : p' ≠ ⊥ := by
      obtain ⟨v, hvp, hv0, hNv⟩ :=
        exists_ne_zero_mem_ker_of_isNilpotent p hp (N i₀) (hnil i₀) (hmaps i₀)
      rw [Submodule.ne_bot_iff]
      exact ⟨v, ⟨hvp, LinearMap.mem_ker.mpr hNv⟩, hv0⟩
    have hmaps' : ∀ i, ∀ x ∈ p', N i x ∈ p' := by
      intro i x hx
      refine ⟨hmaps i x hx.1, ?_⟩
      show N i x ∈ LinearMap.ker (N i₀)
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, (hcomm i₀ i).eq, Module.End.mul_apply,
        LinearMap.mem_ker.mp hx.2, map_zero]
    obtain ⟨v, hvp', hv0, hv⟩ := ih p' hp'ne hmaps'
    refine ⟨v, hvp'.1, hv0, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact LinearMap.mem_ker.mp hvp'.2
    · exact hv i hi

theorem exists_common_ker [IsArtinian R E] [Nontrivial E] {ι : Type*} (N : ι → Module.End R E)
    (hcomm : ∀ i j, Commute (N i) (N j)) (hnil : ∀ i, IsNilpotent (N i)) :
    ∃ v : E, v ≠ 0 ∧ ∀ i, N i v = 0 := by
  classical
  let K : Finset ι → Submodule R E := fun s => ⨅ i ∈ s, LinearMap.ker (N i)
  obtain ⟨m, ⟨s₀, rfl⟩, hmin⟩ :=
    (IsWellFounded.wf : WellFounded ((· < ·) : Submodule R E → Submodule R E → Prop)).has_min
      (Set.range K) ⟨K ∅, ∅, rfl⟩
  have hmemK : ∀ (s : Finset ι) (v : E), v ∈ K s ↔ ∀ i ∈ s, N i v = 0 := by
    intro s v
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker]

  obtain ⟨v, -, hv0, hv⟩ := exists_common_ker_finset N hcomm hnil s₀ ⊤ (by simp)
    (fun i x _ => Submodule.mem_top)
  have hle : ∀ i, K s₀ ≤ LinearMap.ker (N i) := by
    intro i
    have h1 : K (insert i s₀) ≤ K s₀ := by
      intro x hx
      rw [hmemK] at hx ⊢
      exact fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have h2 : ¬ K (insert i s₀) < K s₀ := hmin _ ⟨insert i s₀, rfl⟩
    have h3 : K (insert i s₀) = K s₀ := (eq_or_lt_of_le h1).resolve_right h2
    intro x hx
    rw [← h3, hmemK] at hx
    exact LinearMap.mem_ker.mpr (hx i (Finset.mem_insert_self i s₀))
  refine ⟨v, hv0, fun i => ?_⟩
  exact LinearMap.mem_ker.mp (hle i ((hmemK s₀ v).mpr hv))

end Nilp

section Faithful

variable {𝒪 : Type*} [CommRing 𝒪] {M : Type*} [AddCommGroup M] [Module 𝒪 M]
  {T : Type*} [CommRing T] [Algebra 𝒪 T] {F : Type*} [Field F] [Algebra 𝒪 F]

theorem linearIndependent_coeff {I J : Type*} [Fintype I] [Fintype J]
    (b : Module.Basis I 𝒪 M) (β : Module.Basis J 𝒪 T)
    (act : T →ₐ[𝒪] Module.End 𝒪 M) (hact : Function.Injective act) :
    LinearIndependent 𝒪 (fun j : J => fun p : I × I => b.repr (act (β j) (b p.1)) p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro y hy

  have hzero : act (∑ j, y j • β j) = 0 := by
    apply b.ext
    intro i
    rw [map_sum, LinearMap.sum_apply, LinearMap.zero_apply]
    apply b.repr.injective
    rw [map_sum, map_zero]
    ext k
    have := congr_fun hy (i, k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply]
    convert this using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hsum : ∑ j, y j • β j = 0 := hact (by rw [hzero, map_zero])
  exact (Fintype.linearIndependent_iff.mp β.linearIndependent) y hsum

end Faithful

theorem main
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {M : Type*} [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (act : T →ₐ[𝒪] Module.End 𝒪 M) (hact : Function.Injective act)
    {G : Type*} [CommGroup G] (d : G →* Module.End 𝒪 M)
    (hd : ∀ (g : G) (t : T), d g * act t = act t * d g)
    {F : Type*} [Field F] [IsAlgClosed F] [Algebra 𝒪 F]
    (hF : Function.Injective (algebraMap 𝒪 F)) (lam : T →ₐ[𝒪] F) :
    ∃ (e : G →* Fˣ) (w : F ⊗[𝒪] M), w ≠ 0 ∧
      (∀ t : T, (act t).baseChange F w = lam t • w) ∧
      (∀ g : G, (d g).baseChange F w = ((e g : Fˣ) : F) • w) := by
  classical

  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI : Module.Free 𝒪 M := inferInstance
  haveI : Module.Finite 𝒪 T := Module.Finite.of_injective act.toLinearMap hact
  haveI : Module.IsTorsionFree 𝒪 T :=
    Function.Injective.moduleIsTorsionFree act hact (fun r t => map_smul act r t)
  haveI : Module.Free 𝒪 T := inferInstance
  haveI : FaithfulSMul 𝒪 F := (faithfulSMul_iff_algebraMap_injective 𝒪 F).mpr hF

  let ρT : T →ₐ[𝒪] Module.End F (F ⊗[𝒪] M) := (Module.End.baseChangeHom 𝒪 F M).comp act
  have hρT : ∀ t, ρT t = (act t).baseChange F := fun t => rfl
  let ρ : F ⊗[𝒪] T →ₐ[F] Module.End F (F ⊗[𝒪] M) :=
    Algebra.TensorProduct.lift (Algebra.ofId F _) ρT
      (fun x y => Algebra.commute_algebraMap_left x (ρT y))
  have hρ : ∀ (c : F) (t : T), ρ (c ⊗ₜ t) = c • (act t).baseChange F := by
    intro c t
    show Algebra.ofId F _ c * ρT t = _
    rw [Algebra.ofId_apply, ← Algebra.smul_def]
    rfl
  let lamF : F ⊗[𝒪] T →ₐ[F] F :=
    Algebra.TensorProduct.lift (AlgHom.id F F) lam (fun x y => Commute.all x _)
  have hlamF : ∀ (c : F) (t : T), lamF (c ⊗ₜ t) = c * lam t := fun c t => rfl

  have hρinj : Function.Injective ρ := by
    let b := Module.Free.chooseBasis 𝒪 M
    let β := Module.Free.chooseBasis 𝒪 T
    let bF := Algebra.TensorProduct.basis F b
    let βF := Algebra.TensorProduct.basis F β
    have hli := (linearIndependent_algebraMap_comp_iff (S := F)).mpr
      (linearIndependent_coeff b β act hact)
    rw [injective_iff_map_eq_zero]
    intro x hx

    have hxrepr : x = ∑ j, βF.repr x j • ((1 : F) ⊗ₜ β j) := by
      conv_lhs => rw [← βF.sum_repr x]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.basis_apply]

    have hcoef : ∑ j, βF.repr x j • (algebraMap 𝒪 F ∘ fun p : _ × _ =>
        b.repr (act (β j) (b p.1)) p.2) = 0 := by
      ext ⟨i, k⟩
      have h1 : ρ x (bF i) = 0 := by rw [hx, LinearMap.zero_apply]
      rw [hxrepr, map_sum, LinearMap.sum_apply] at h1
      have h2 : bF.repr (∑ j, ρ (βF.repr x j • ((1 : F) ⊗ₜ β j)) (bF i)) k = 0 := by
        rw [h1, map_zero, Finsupp.zero_apply]
      rw [map_sum, Finsupp.finsetSum_apply] at h2
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        Pi.zero_apply]
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, hρ, one_smul, Algebra.TensorProduct.basis_apply,
        LinearMap.baseChange_tmul, map_smul, Finsupp.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
    have hd : ∀ j, βF.repr x j = 0 := fun j =>
      (Fintype.linearIndependent_iff.mp hli) (fun j => βF.repr x j) hcoef j
    rw [hxrepr]
    simp [hd]

  let f : T ⊕ G → Module.End F (F ⊗[𝒪] M) :=
    Sum.elim (fun t => (act t).baseChange F) (fun g => (d g).baseChange F)
  have hcommTT : ∀ s t : T, act s * act t = act t * act s := fun s t => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hcommGG : ∀ g h : G, d g * d h = d h * d g := fun g h => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hbc : ∀ (u v : Module.End 𝒪 M), u * v = v * u →
      Commute (u.baseChange F) (v.baseChange F) := by
    intro u v huv
    show u.baseChange F * v.baseChange F = v.baseChange F * u.baseChange F
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, huv]
  have hfcomm : ∀ i j, Commute (f i) (f j) := by
    rintro (s | g) (t | h)
    · exact hbc _ _ (hcommTT s t)
    · exact hbc _ _ (hd h s).symm
    · exact hbc _ _ (hd g t)
    · exact hbc _ _ (hcommGG g h)
  let E : (T ⊕ G → F) → Submodule F (F ⊗[𝒪] M) := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i)
  have hE : ∀ χ, E χ = ⨅ i, (f i).maxGenEigenspace (χ i) := fun χ => rfl
  have hmaps : ∀ i j (φ : F), Set.MapsTo (f i) ((f j).maxGenEigenspace φ)
      ((f j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfcomm j i) φ
  have htop : ⨆ χ, E χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo f hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hind : iSupIndep E := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps

  have key : ∃ χ : T ⊕ G → F, (∀ t, χ (Sum.inl t) = lam t) ∧ E χ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    letI : Fintype {χ // E χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
    have hbad : ∀ χ : {χ // E χ ≠ ⊥}, ∃ t : T, χ.1 (Sum.inl t) ≠ lam t := by
      intro χ
      by_contra h
      push Not at h
      exact χ.2 (hcon χ.1 h)
    choose tχ htχ using hbad
    set n := Module.finrank F (F ⊗[𝒪] M) with hn
    let fac : {χ // E χ ≠ ⊥} → F ⊗[𝒪] T := fun χ =>
      ((1 : F) ⊗ₜ tχ χ - algebraMap F (F ⊗[𝒪] T) (χ.1 (Sum.inl (tχ χ)))) ^ n
    let p : F ⊗[𝒪] T := ∏ χ, fac χ

    have hfac : ∀ (χ : {χ // E χ ≠ ⊥}), ∀ v ∈ E χ.1, ρ (fac χ) v = 0 := by
      intro χ v hv
      have hv' : v ∈ (f (Sum.inl (tχ χ))).maxGenEigenspace (χ.1 (Sum.inl (tχ χ))) :=
        (iInf_le (fun i => (f i).maxGenEigenspace (χ.1 i)) (Sum.inl (tχ χ))) hv
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
        Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hv'
      have hρfac : ρ (fac χ) = ((act (tχ χ)).baseChange F -
          algebraMap F (Module.End F (F ⊗[𝒪] M)) (χ.1 (Sum.inl (tχ χ)))) ^ n := by
        simp only [fac, map_pow, map_sub, AlgHom.commutes]
        rw [hρ, one_smul]
      rw [hρfac]
      convert hv' using 2
      rw [hn, Algebra.algebraMap_eq_smul_one]
      rfl
    have hkill : ∀ (χ : T ⊕ G → F), ∀ v ∈ E χ, ρ p v = 0 := by
      intro χ v hv
      by_cases hχ : E χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hv
        rw [hv, map_zero]
      · let χ' : {χ // E χ ≠ ⊥} := ⟨χ, hχ⟩
        have hp : p = (∏ x ∈ Finset.univ.erase χ', fac x) * fac χ' :=
          (Finset.prod_erase_mul Finset.univ fac (Finset.mem_univ χ')).symm
        rw [hp, map_mul, Module.End.mul_apply, hfac χ' v hv, map_zero]
    have hρp : ρ p = 0 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ ⨆ χ, E χ := by rw [htop]; exact Submodule.mem_top
      rw [LinearMap.zero_apply]
      refine Submodule.iSup_induction E (motive := fun v => ρ p v = 0) hv hkill (map_zero _) ?_
      intro x y hx hy
      rw [map_add, hx, hy, add_zero]
    have hp0 : p = 0 := hρinj (by rw [hρp, map_zero])
    have hlamp : lamF p = ∏ χ, (lam (tχ χ) - χ.1 (Sum.inl (tχ χ))) ^ n := by
      simp only [p, fac, map_prod, map_pow, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
      refine Finset.prod_congr rfl fun χ _ => ?_
      rw [hlamF, one_mul]
    have hne : lamF p ≠ 0 := by
      rw [hlamp, Finset.prod_ne_zero_iff]
      intro χ _
      exact pow_ne_zero _ (sub_ne_zero.mpr (htχ χ).symm)
    exact hne (by rw [hp0, map_zero])
  obtain ⟨χ, hχ, hEχ⟩ := key

  haveI : Nontrivial (E χ) := Submodule.nontrivial_iff_ne_bot.mpr hEχ
  have hmapsE : ∀ i, Set.MapsTo (f i - algebraMap F (Module.End F (F ⊗[𝒪] M)) (χ i))
      (E χ) (E χ) := by
    intro i v hv
    have hv' : v ∈ E χ := hv
    have hfi : f i v ∈ E χ := by
      rw [hE, Submodule.mem_iInf] at hv' ⊢
      exact fun j => hmaps i j (χ j) (hv' j)
    exact (E χ).sub_mem hfi ((E χ).smul_mem _ hv')
  let N : T ⊕ G → Module.End F (E χ) := fun i => (f i - algebraMap F _ (χ i)).restrict (hmapsE i)
  have hNcomm : ∀ i j, Commute (N i) (N j) := by
    intro i j
    have hc : Commute (f i - algebraMap F (Module.End F (F ⊗[𝒪] M)) (χ i))
        (f j - algebraMap F (Module.End F (F ⊗[𝒪] M)) (χ j)) :=
      Commute.sub_left (R := Module.End F (F ⊗[𝒪] M))
        (Commute.sub_right (R := Module.End F (F ⊗[𝒪] M)) (hfcomm i j)
          (Algebra.commute_algebraMap_right _ _))
        (Algebra.commute_algebraMap_left _ _)
    ext ⟨v, hv⟩
    exact congrArg Subtype.val (show (N i * N j) ⟨v, hv⟩ = (N j * N i) ⟨v, hv⟩ from
      Subtype.ext (LinearMap.congr_fun hc.eq v))
  have hNnil : ∀ i, IsNilpotent (N i) := by
    intro i
    exact Module.End.isNilpotent_restrict_of_le (q := (f i).maxGenEigenspace (χ i))
      (hq := Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes (f i) (χ i)) (χ i))
      (iInf_le (fun j => (f j).maxGenEigenspace (χ j)) i)
      (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f i) (χ i))
  obtain ⟨v, hv0, hv⟩ := exists_common_ker (R := F) (E := ↥(E χ)) N hNcomm hNnil
  have hw0 : (v : F ⊗[𝒪] M) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have heig : ∀ i, f i v = χ i • (v : F ⊗[𝒪] M) := by
    intro i
    have := congrArg Subtype.val (hv i)
    simp only [N, LinearMap.coe_restrict_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply, ZeroMemClass.coe_zero] at this
    exact sub_eq_zero.mp this

  have hunit : ∀ g, χ (Sum.inr g) ≠ 0 := by
    intro g h0
    have h1 : (d g).baseChange F v = 0 := by
      have := heig (Sum.inr g)
      simp only [f, Sum.elim_inr] at this
      rw [this, h0, zero_smul]
    have h2 : (d g⁻¹).baseChange F ((d g).baseChange F v) = (v : F ⊗[𝒪] M) := by
      rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, ← map_mul, inv_mul_cancel, map_one,
        LinearMap.baseChange_one, Module.End.one_apply]
    rw [h1, map_zero] at h2
    exact hw0 h2.symm
  have hmul : ∀ g h, χ (Sum.inr (g * h)) = χ (Sum.inr g) * χ (Sum.inr h) := by
    intro g h
    apply smul_left_injective F hw0
    have e1 := heig (Sum.inr (g * h))
    have e2 := heig (Sum.inr g)
    have e3 := heig (Sum.inr h)
    simp only [f, Sum.elim_inr] at e1 e2 e3
    show χ (Sum.inr (g * h)) • (v : F ⊗[𝒪] M) = (χ (Sum.inr g) * χ (Sum.inr h)) • (v : F ⊗[𝒪] M)
    rw [← e1, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, e3, map_smul, e2, smul_smul,
      mul_comm]
  have hone : χ (Sum.inr 1) = 1 := by
    apply smul_left_injective F hw0
    have e1 := heig (Sum.inr 1)
    simp only [f, Sum.elim_inr, map_one, LinearMap.baseChange_one, Module.End.one_apply] at e1
    show χ (Sum.inr 1) • (v : F ⊗[𝒪] M) = (1 : F) • (v : F ⊗[𝒪] M)
    rw [← e1, one_smul]
  let e : G →* Fˣ :=
    { toFun := fun g => Units.mk0 (χ (Sum.inr g)) (hunit g)
      map_one' := Units.ext hone
      map_mul' := fun g h => Units.ext (hmul g h) }
  refine ⟨e, v, hw0, fun t => ?_, fun g => ?_⟩
  · have := heig (Sum.inl t)
    simp only [f, Sum.elim_inl] at this
    rw [this, hχ t]
  · have := heig (Sum.inr g)
    simp only [f, Sum.elim_inr] at this
    rw [this]
    rfl

end DeligneSerre.OperatorAlgebra.PointLemma

theorem solution
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {M : Type*} [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {T : Type*} [CommRing T] [Algebra 𝒪 T]
    (act : T →ₐ[𝒪] Module.End 𝒪 M) (hact : Function.Injective act)
    {G : Type*} [CommGroup G] (d : G →* Module.End 𝒪 M)
    (hd : ∀ (g : G) (t : T), d g * act t = act t * d g)
    {F : Type*} [Field F] [IsAlgClosed F] [Algebra 𝒪 F]
    (hF : Function.Injective (algebraMap 𝒪 F)) (lam : T →ₐ[𝒪] F) :
    ∃ (e : G →* Fˣ) (w : F ⊗[𝒪] M), w ≠ 0 ∧
      (∀ t : T, (act t).baseChange F w = lam t • w) ∧
      (∀ g : G, (d g).baseChange F w = ((e g : Fˣ) : F) • w) :=
  DeligneSerre.OperatorAlgebra.PointLemma.main act hact d hd hF lam

end S_DeligneSerre_OperatorAlgebra_exists_eigenvector_baseChange_of_algHom
end P2MW
export P2MW.S_DeligneSerre_OperatorAlgebra_exists_eigenvector_baseChange_of_algHom (solution)
