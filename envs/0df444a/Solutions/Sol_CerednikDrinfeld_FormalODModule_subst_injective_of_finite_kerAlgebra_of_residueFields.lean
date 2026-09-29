-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_residueFields
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2b3a0baa-569d-59b7-ba1e-84c97768ac4d

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace H2Aux

theorem finite_kerAlgebra_map {B C : Type u} [CommRing B] [CommRing C] (φ : Series B)
    (hφ : Module.Finite B (FormalODModule.KerAlgebra φ)) (g : B →+* C) (hg : Function.Surjective g) :
    Module.Finite C (FormalODModule.KerAlgebra (φ.map g)) := by
  classical
  let I : Ideal (MvPowerSeries (Fin 2) B) := Ideal.span (Set.range φ)
  let J : Ideal (MvPowerSeries (Fin 2) C) := Ideal.span (Set.range (φ.map g))

  have hIJ : ∀ a ∈ I, (Ideal.Quotient.mk J).comp (MvPowerSeries.map g) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    refine Submodule.span_induction (p := fun a _ => (MvPowerSeries.map g) a ∈ J) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨i, rfl⟩
      exact Ideal.subset_span ⟨i, rfl⟩
    · simp
    · intro x y _ _ hx hy; simpa using J.add_mem hx hy
    · intro r x _ hx; simpa using J.mul_mem_left ((MvPowerSeries.map g) r) hx
  let Ψ : FormalODModule.KerAlgebra φ →+* FormalODModule.KerAlgebra (φ.map g) :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp (MvPowerSeries.map g)) hIJ
  have hmapsurj : Function.Surjective (MvPowerSeries.map (σ := Fin 2) g) := by
    intro F
    refine ⟨fun e => Function.surjInv hg (F e), ?_⟩
    ext e
    rw [MvPowerSeries.coeff_map]
    exact Function.surjInv_eq hg _
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    obtain ⟨Fy, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨Fx, rfl⟩ := hmapsurj Fy
    exact ⟨Ideal.Quotient.mk I Fx, rfl⟩

  letI algBC : Algebra B C := g.toAlgebra
  have hΨalg : ∀ b : B, Ψ (algebraMap B (FormalODModule.KerAlgebra φ) b) =
      algebraMap B (FormalODModule.KerAlgebra (φ.map g)) b := by
    intro b
    change Ideal.Quotient.mk J (MvPowerSeries.map g (algebraMap B (MvPowerSeries (Fin 2) B) b)) =
      Ideal.Quotient.mk J (algebraMap B (MvPowerSeries (Fin 2) C) b)
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.map_C]
    rfl
  let ΨB : FormalODModule.KerAlgebra φ →ₐ[B] FormalODModule.KerAlgebra (φ.map g) :=
    { toRingHom := Ψ, commutes' := hΨalg }
  haveI : Module.Finite B (FormalODModule.KerAlgebra (φ.map g)) :=
    Module.Finite.of_surjective ΨB.toLinearMap hΨsurj
  exact Module.Finite.of_restrictScalars_finite B C (FormalODModule.KerAlgebra (φ.map g))

theorem coeff_subst_mem {B : Type u} [CommRing B] (φ : Series B) (hφ : MvPowerSeries.HasSubst φ)
    (I : Ideal B) (d : MvPowerSeries (Fin 2) B) (hd : ∀ e, MvPowerSeries.coeff e d ∈ I) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst φ d) ∈ I := by
  rw [MvPowerSeries.coeff_subst hφ]
  refine finsum_induction (fun x => x ∈ I) I.zero_mem (fun a b ha hb => I.add_mem ha hb) fun i => ?_
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (hd i)

theorem eq_zero_of_subst_eq_zero_local {L : Type u} [CommRing L] [IsNoetherianRing L] [IsLocalRing L]
    (φ : Series L) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hinj : ∀ f' : MvPowerSeries (Fin 2) (IsLocalRing.ResidueField L),
      MvPowerSeries.subst (φ.map (IsLocalRing.residue L)) f' = 0 → f' = 0)
    (d : MvPowerSeries (Fin 2) L) (hd : MvPowerSeries.subst φ d = 0) : d = 0 := by
  classical
  have hφs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hφks : MvPowerSeries.HasSubst (φ.map (IsLocalRing.residue L)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map (IsLocalRing.residue L) (φ i)) = 0
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, map_zero]
  set 𝔪 : Ideal L := IsLocalRing.maximalIdeal L with h𝔪

  have step : ∀ n : ℕ, ∀ e, MvPowerSeries.coeff e d ∈ 𝔪 ^ n := by
    intro n
    induction n with
    | zero => intro e; simp
    | succ n ih =>

      let M : Submodule L L := 𝔪 ^ n
      let N' : Submodule L M := Submodule.comap M.subtype (𝔪 ^ (n + 1))
      let V := M ⧸ N'
      let π : M →ₗ[L] V := N'.mkQ
      have hmemN : ∀ (a : L) (m : M), a ∈ 𝔪 → a • m ∈ N' := by
        intro a m ha
        show (a • m : M).1 ∈ 𝔪 ^ (n + 1)
        rw [pow_succ']
        exact Ideal.mul_mem_mul ha m.2
      have hV : Module.IsTorsionBySet L V (↑(IsLocalRing.maximalIdeal L) : Set L) := by
        rintro x ⟨a, ha⟩
        obtain ⟨m, rfl⟩ := N'.mkQ_surjective x
        show a • N'.mkQ m = 0
        rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmemN a m (by rw [h𝔪]; exact ha)
      letI modk : Module (IsLocalRing.ResidueField L) V := hV.module

      have hfun : ∀ (lam : Module.Dual (IsLocalRing.ResidueField L) V) (e : Fin 2 →₀ ℕ),
          lam (π ⟨MvPowerSeries.coeff e d, ih e⟩) = 0 := by
        intro lam
        let dl : MvPowerSeries (Fin 2) (IsLocalRing.ResidueField L) := fun e => lam (π ⟨MvPowerSeries.coeff e d, ih e⟩)
        have hdl : ∀ e, MvPowerSeries.coeff e dl = lam (π ⟨MvPowerSeries.coeff e d, ih e⟩) := fun e => rfl
        suffices hz : MvPowerSeries.subst (φ.map (IsLocalRing.residue L)) dl = 0 by
          intro e; rw [← hdl, hinj dl hz, MvPowerSeries.coeff_zero]
        ext e
        rw [MvPowerSeries.coeff_zero, MvPowerSeries.coeff_subst hφks]

        let fam : (Fin 2 →₀ ℕ) → M := fun e' =>
          MvPowerSeries.coeff e (e'.prod fun s m => φ s ^ m) • (⟨MvPowerSeries.coeff e' d, ih e'⟩ : M)
        have hprodmap : ∀ e' : Fin 2 →₀ ℕ,
            MvPowerSeries.coeff e (e'.prod fun s m => (φ.map (IsLocalRing.residue L)) s ^ m) =
              IsLocalRing.residue L (MvPowerSeries.coeff e (e'.prod fun s m => φ s ^ m)) := by
          intro e'
          rw [← MvPowerSeries.coeff_map]
          congr 1
          simp only [Finsupp.prod, map_prod, map_pow]
          rfl
        have hterm : ∀ e', MvPowerSeries.coeff e' dl • MvPowerSeries.coeff e (e'.prod fun s m => (φ.map (IsLocalRing.residue L)) s ^ m)
            = lam (π (fam e')) := by
          intro e'
          rw [hdl, hprodmap, smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul]
          rfl
        simp_rw [hterm]

        have hfamval : ∀ e', (fam e').1 =
            MvPowerSeries.coeff e' d • MvPowerSeries.coeff e (e'.prod fun s m => φ s ^ m) := by
          intro e'
          show MvPowerSeries.coeff e (e'.prod fun s m => φ s ^ m) * MvPowerSeries.coeff e' d = _
          rw [smul_eq_mul, mul_comm]
        have hfam : (Function.support fam).Finite := by
          refine (MvPowerSeries.coeff_subst_finite hφs d e).subset fun e' he' => ?_
          rw [Function.mem_support] at he' ⊢
          intro h0; apply he'
          apply Subtype.ext; rw [hfamval, h0]; rfl
        have hexch : lam (π (∑ᶠ e', fam e')) = ∑ᶠ e', lam (π (fam e')) :=
          AddMonoidHom.map_finsum (lam.toAddMonoidHom.comp π.toAddMonoidHom) hfam
        rw [← hexch]
        have hsum : (∑ᶠ e', fam e') = 0 := by
          apply Subtype.ext
          have h1 : ((∑ᶠ e', fam e') : M).1 = ∑ᶠ e', (fam e').1 :=
            AddMonoidHom.map_finsum M.subtype.toAddMonoidHom hfam
          have h2 : ∑ᶠ e', (fam e').1 = MvPowerSeries.coeff e (MvPowerSeries.subst φ d) := by
            rw [MvPowerSeries.coeff_subst hφs]; exact finsum_congr hfamval
          rw [h1, h2, hd, MvPowerSeries.coeff_zero]; rfl
        rw [hsum, map_zero, map_zero]
      intro e
      have hzero : π ⟨MvPowerSeries.coeff e d, ih e⟩ = 0 :=
        (Module.forall_dual_apply_eq_zero_iff (IsLocalRing.ResidueField L) _).mp (fun lam => hfun lam e)
      have : (⟨MvPowerSeries.coeff e d, ih e⟩ : M) ∈ N' := by
        rwa [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      exact this
  ext e
  rw [MvPowerSeries.coeff_zero]
  have hmem : MvPowerSeries.coeff e d ∈ ⨅ n : ℕ, 𝔪 ^ n := Submodule.mem_iInf _ |>.mpr fun n => step n e
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing 𝔪 (by rw [h𝔪]; exact Ideal.IsPrime.ne_top inferInstance),
    Submodule.mem_bot] at hmem

end H2Aux

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : Module.Finite B (FormalODModule.KerAlgebra φ))
    (hres : ∀ (κ : Type u) [Field κ] (g : B →+* κ), Function.Surjective g →
      Module.Finite κ (FormalODModule.KerAlgebra (φ.map g)) →
      ∀ f' g' : MvPowerSeries (Fin 2) κ,
        MvPowerSeries.subst (φ.map g) f' = MvPowerSeries.subst (φ.map g) g' → f' = g')
    (f g : MvPowerSeries (Fin 2) B) (h : MvPowerSeries.subst φ f = MvPowerSeries.subst φ g) : f = g := by
  classical
  have hφs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0

  suffices key : ∀ d : MvPowerSeries (Fin 2) B, MvPowerSeries.subst φ d = 0 → d = 0 by
    have := key (f - g) (by rw [MvPowerSeries.subst_sub hφs, h, sub_self])
    exact sub_eq_zero.mp this
  intro d hd
  ext e
  rw [MvPowerSeries.coeff_zero]
  refine eq_zero_of_localization _ fun 𝔪 h𝔪 => ?_

  let L := Localization.AtPrime 𝔪
  let ι : B →+* L := algebraMap B L
  have hdL : MvPowerSeries.subst (φ.map ι) (MvPowerSeries.map ι d) = 0 := by
    have := congrArg (MvPowerSeries.map ι) hd
    rwa [MvPowerSeries.map_subst hφs, map_zero] at this
  have hφL0 : ∀ i, MvPowerSeries.constantCoeff ((φ.map ι) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map ι (φ i)) = 0
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, map_zero]

  have hsurj : Function.Surjective ((IsLocalRing.residue L).comp ι) := by
    haveI := h𝔪
    intro y
    obtain ⟨xbar, hx⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 L).surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
    exact ⟨x, by rw [← hx, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]; rfl⟩
  have hinj : ∀ f' : MvPowerSeries (Fin 2) (IsLocalRing.ResidueField L),
      MvPowerSeries.subst ((φ.map ι).map (IsLocalRing.residue L)) f' = 0 → f' = 0 := by
    intro f' hf'
    have hmm : (φ.map ι).map (IsLocalRing.residue L) = φ.map ((IsLocalRing.residue L).comp ι) := by
      funext i; show MvPowerSeries.map _ (MvPowerSeries.map _ (φ i)) = MvPowerSeries.map _ (φ i)
      rw [MvPowerSeries.map_map]
    rw [hmm] at hf'
    have hφκ : MvPowerSeries.HasSubst (φ.map ((IsLocalRing.residue L).comp ι)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
        show MvPowerSeries.constantCoeff (MvPowerSeries.map ((IsLocalRing.residue L).comp ι) (φ i)) = 0
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, map_zero]
    refine hres _ ((IsLocalRing.residue L).comp ι) hsurj
      (H2Aux.finite_kerAlgebra_map φ hφ _ hsurj) f' 0 ?_
    rw [hf', ← MvPowerSeries.coe_substAlgHom hφκ, map_zero]
  have := H2Aux.eq_zero_of_subst_eq_zero_local (φ.map ι) hφL0 hinj (MvPowerSeries.map ι d) hdL
  have := congrArg (MvPowerSeries.coeff e) this
  rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_zero] at this

end S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields (solution)
