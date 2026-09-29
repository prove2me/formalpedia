-- Prove2me | solution 1 for ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_Kw_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/73eba157-802a-5559-90f0-2647bcd36bde

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsLocalRing_finrank_invariants_linHom_fieldUnits_modPow_eq
import Theorems.Thm_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff
import Theorems.Thm_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finiteIndex_toAddSubgroup_span_pow_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_principalUnits_Rw
import Theorems.Thm_ExtCitation_LocalLevel_index_principalUnits_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_valuation_units_Kw
import Theorems.Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
import Theorems.Thm_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open Module
open scoped IntermediateField Pointwise

open ExtCitation.LocalLevel _root_.IsLocalRing _root_.Module.IsLocalRing in

set_option maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ q ∣ Fintype.card Δ) (act : Δ →* (Kw ≃ₐ[ℚ_[q]] Kw))
    {ι : Type*} [Fintype ι] (w : Δ × ι → Kw) (hwR : ∀ x, w x ∈ Rw q Kw) (hw : LinearIndependent ℚ_[q] w)
    (hcard : Fintype.card (Δ × ι) = Module.finrank ℚ_[q] Kw)
    (hperm : ∀ (d d' : Δ) (i : ι), act d (w (d', i)) = w (d * d', i))
    {VN : Type*} [AddCommGroup VN] [Module (ZMod q) VN] [FiniteDimensional (ZMod q) VN]
    (N : Representation (ZMod q) Δ VN)
    {VPF : Type*} [AddCommGroup VPF] [Module (ZMod q) VPF] (PF : Representation (ZMod q) Δ VPF)
    (πF : Additive (↥Kw)ˣ →+ VPF) (hπF : Function.Surjective πF)
    (hkerπF : ∀ u : (↥Kw)ˣ, πF (Additive.ofMul u) = 0 ↔ ∃ w : (↥Kw)ˣ, w ^ q = u)
    (hπFΔ : ∀ (d : Δ) (u : (↥Kw)ˣ),
      πF (Additive.ofMul (Units.map (act d : Kw →* Kw) u)) = PF d (πF (Additive.ofMul u)))
    {VTF : Type*} [AddCommGroup VTF] [Module (ZMod q) VTF] (TF : Representation (ZMod q) Δ VTF)
    (ιF : VTF →+ Additive (↥Kw)ˣ) (hιF : Function.Injective ιF)
    (hranιF : ∀ u : (↥Kw)ˣ, Additive.ofMul u ∈ Set.range ιF ↔ u ^ q = 1)
    (hιFΔ : ∀ (d : Δ) (v : VTF),
      Additive.toMul (ιF (TF d v)) = Units.map (act d : Kw →* Kw) (Additive.toMul (ιF v))) :
    finrank (ZMod q) (N.linHom PF).invariants
      = Fintype.card ι * finrank (ZMod q) VN + finrank (ZMod q) (N.linHom TF).invariants
        + finrank (ZMod q) (N.linHom (Representation.trivial (ZMod q) Δ (ZMod q))).invariants := by
  classical
  have hqF : (q : Kw) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

  let actF : Δ →* (Kw ≃+* Kw) :=
    { toFun := fun d => (act d : Kw ≃+* Kw)
      map_one' := by simp only [map_one]; rfl
      map_mul' := fun _ _ => by simp only [map_mul]; rfl }
  have actF_apply : ∀ (d : Δ) (x : Kw), actF d x = act d x := fun _ _ => rfl

  let ρR : Δ → (Rw q Kw ≃+* Rw q Kw) := fun d =>
    { toFun := fun x => ⟨act d x, (algEquiv_apply_mem_Rw_iff q Kw (act d) x).mpr x.2⟩
      invFun := fun x => ⟨(act d).symm x, by
        have h := algEquiv_apply_mem_Rw_iff q Kw (act d) ((act d).symm x)
        rw [AlgEquiv.apply_symm_apply] at h
        exact h.mp x.2⟩
      left_inv := fun x => Subtype.ext ((act d).symm_apply_apply x)
      right_inv := fun x => Subtype.ext ((act d).apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (map_mul (act d) _ _)
      map_add' := fun x y => Subtype.ext (map_add (act d) _ _) }
  let actR : Δ →* (Rw q Kw ≃+* Rw q Kw) :=
    { toFun := ρR
      map_one' := by
        apply RingEquiv.ext; intro x; apply Subtype.ext
        show (act 1) (x : Kw) = x
        rw [map_one]; rfl
      map_mul' := fun d d' => by
        apply RingEquiv.ext; intro x; apply Subtype.ext
        show (act (d * d')) (x : Kw) = act d (act d' x)
        rw [map_mul]; rfl }
  have act_coe : ∀ (d : Δ) (x : Rw q Kw), ((actR d x : Rw q Kw) : Kw) = act d x := fun _ _ => rfl

  obtain ⟨e, f, he0, hf0, hspan, hcardres, hef, hpowall, hnotorsall⟩ := exists_ramification_principalUnits_Rw q Kw
  have hfin : ∀ n : ℕ, (maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.FiniteIndex := fun n =>
    (index_toAddSubgroup_maximalIdeal_pow_Rw q Kw n).1
  have hidxm : (principalUnits (Rw q Kw) (e + 1)).FiniteIndex := (index_principalUnits_Rw q Kw (k := e + 1) (by omega)).1
  have hidxme : (principalUnits (Rw q Kw) (e + 1 + e)).FiniteIndex :=
    (index_principalUnits_Rw q Kw (k := e + 1 + e) (by omega)).1

  obtain ⟨v, hv, hvker, hvΔ, -⟩ := exists_valuation_units_Kw q Kw

  obtain ⟨N₀, hN₀⟩ := exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw q Kw w hw hcard
  let S : Submodule ℤ_[q] Kw := Submodule.span ℤ_[q] (Set.range w)
  have hsmulR : ∀ (c : ℤ_[q]) (x : Kw), x ∈ Rw q Kw → c • x ∈ Rw q Kw := by
    intro c x hx
    rw [mem_Rw_iff_isIntegral] at hx ⊢
    have : ((c • x : Kw) : PadicAlgCl q) = algebraMap ℤ_[q] (PadicAlgCl q) c * (x : PadicAlgCl q) := by
      rw [IntermediateField.coe_smul, Algebra.smul_def]
    rw [this]
    exact IsIntegral.mul isIntegral_algebraMap hx
  have hSR : ∀ x : Kw, x ∈ S → x ∈ Rw q Kw := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hwR j
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact hsmulR c x hx

  have hact_smul : ∀ (d : Δ) (c : ℤ_[q]) (x : Kw), act d (c • x) = c • act d x := by
    intro d c x
    rw [← IsScalarTower.algebraMap_smul ℚ_[q] c x, Algebra.smul_def, map_mul, AlgEquiv.commutes,
      ← Algebra.smul_def, IsScalarTower.algebraMap_smul]
  have hSstab : ∀ (d : Δ) (x : Kw), x ∈ S → act d x ∈ S := by
    intro d x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨d', i⟩, rfl⟩ := hx
      rw [hperm]
      exact Submodule.subset_span ⟨(d * d', i), rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [hact_smul]; exact Submodule.smul_mem _ _ hx
  let Λ : AddSubgroup (Rw q Kw) := S.toAddSubgroup.comap ((algebraMap (Rw q Kw) Kw : Rw q Kw →+* Kw) : Rw q Kw →+ Kw)
  have hΛmem : ∀ x : Rw q Kw, x ∈ Λ ↔ (x : Kw) ∈ S := fun _ => Iff.rfl
  haveI : Λ.FiniteIndex := by
    haveI := finiteIndex_toAddSubgroup_span_pow_Rw q Kw N₀
    apply AddSubgroup.finiteIndex_of_le (H := (Ideal.span {((q : ℕ) : Rw q Kw) ^ N₀}).toAddSubgroup)
    intro x hx
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [hΛmem]
    have hy := hN₀ (y : Kw) y.2
    have : ((y * (q : Rw q Kw) ^ N₀ : Rw q Kw) : Kw) = ((q : ℚ_[q]) ^ N₀) • (y : Kw) := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
      push_cast
      ring
    rw [this]
    exact hy
  have hΛ : ∀ (d : Δ) (x : Rw q Kw), x ∈ Λ → actR d x ∈ Λ := by
    intro d x hx
    rw [hΛmem, act_coe]
    exact hSstab d x ((hΛmem x).mp hx)

  have hwint : LinearIndependent ℤ_[q] w :=
    hw.restrict_scalars (by
      intro a b h
      apply Subtype.ext
      have : (a : ℚ_[q]) • (1 : ℚ_[q]) = (b : ℚ_[q]) • 1 := h
      simpa using this)
  let bS : Module.Basis (Δ × ι) ℤ_[q] S := Module.Basis.span hwint
  have hbS : ∀ j, (bS j : Kw) = w j := fun j => congrArg Subtype.val (Module.Basis.span_apply hwint j)
  let σS : Δ → (S →ₗ[ℤ_[q]] S) := fun d =>
    { toFun := fun s => ⟨act d s, hSstab d s s.2⟩
      map_add' := fun s t => Subtype.ext (map_add (act d) _ _)
      map_smul' := fun c s => Subtype.ext (hact_smul d c s) }
  have hσS_b : ∀ (d d' : Δ) (i : ι), σS d (bS (d', i)) = bS (d * d', i) := by
    intro d d' i
    apply Subtype.ext
    show act d (bS (d', i) : Kw) = (bS (d * d', i) : Kw)
    rw [hbS, hbS, hperm]
  have hrepr : ∀ (d : Δ) (s : S),
      bS.repr (σS d s) = Finsupp.mapDomain (fun x : Δ × ι => (d * x.1, x.2)) (bS.repr s) := by
    intro d
    suffices h : bS.repr.toLinearMap ∘ₗ σS d
        = (Finsupp.lmapDomain ℤ_[q] ℤ_[q] (fun x : Δ × ι => (d * x.1, x.2))) ∘ₗ bS.repr.toLinearMap from
      fun s => LinearMap.congr_fun h s
    apply bS.ext
    rintro ⟨d', i⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hσS_b, Module.Basis.repr_self,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

  let VΛ := Δ × ι →₀ ZMod q
  let red : (Δ × ι →₀ ℤ_[q]) →+ VΛ := Finsupp.mapRange.addMonoidHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q).toAddMonoidHom
  have hred : ∀ c, red c = Finsupp.mapRange PadicInt.toZMod (map_zero _) c := fun _ => rfl
  let toS : Λ →+ S :=
    { toFun := fun x => ⟨((x : Rw q Kw) : Kw), (hΛmem _).mp x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have htoS_surj : Function.Surjective toS := fun s => ⟨⟨⟨s, hSR s s.2⟩, (hΛmem _).mpr s.2⟩, rfl⟩
  have htoS_inj : Function.Injective toS := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun s : S => (s : Kw)) h))
  let πΛ : Λ →+ VΛ := red.comp (bS.repr.toLinearMap.toAddMonoidHom.comp toS)
  have hπΛ_apply : ∀ x, πΛ x = red (bS.repr (toS x)) := fun _ => rfl
  let PΛ : Representation (ZMod q) Δ VΛ :=
    { toFun := fun d => Finsupp.lmapDomain (ZMod q) (ZMod q) (fun x : Δ × ι => (d * x.1, x.2))
      map_one' := by
        apply LinearMap.ext; intro c
        simp only [one_mul, Prod.mk.eta, Finsupp.lmapDomain_apply, Module.End.one_apply]
        try exact Finsupp.mapDomain_id
      map_mul' := fun d d' => by
        apply LinearMap.ext; intro c
        simp only [Finsupp.lmapDomain_apply, Module.End.mul_apply, ← Finsupp.mapDomain_comp, Function.comp_def,
          mul_assoc] }
  have hPΛ : ∀ d (c : VΛ), PΛ d c = Finsupp.mapDomain (fun x : Δ × ι => (d * x.1, x.2)) c := fun _ _ => rfl
  let b : Module.Basis (Δ × ι) (ZMod q) VΛ := Finsupp.basisSingleOne
  have hb : ∀ (d d' : Δ) (i : ι), PΛ d (b (d', i)) = b (d * d', i) := by
    intro d d' i
    rw [hPΛ]
    show Finsupp.mapDomain _ (Finsupp.single (d', i) 1) = Finsupp.single (d * d', i) 1
    rw [Finsupp.mapDomain_single]

  have htoZMod_surj : Function.Surjective (PadicInt.toZMod : ℤ_[q] → ZMod q) := fun z =>
    ⟨(z.val : ℤ_[q]), by rw [map_natCast, ZMod.natCast_zmod_val]⟩
  have hred_surj : Function.Surjective red := fun c => by
    obtain ⟨c₂, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero _) htoZMod_surj c
    exact ⟨c₂, rfl⟩
  have hπΛ_surj : Function.Surjective πΛ := by
    intro c
    obtain ⟨c', rfl⟩ := hred_surj c
    obtain ⟨x, hx⟩ := htoS_surj (bS.repr.symm c')
    exact ⟨x, by rw [hπΛ_apply, hx, LinearEquiv.apply_symm_apply]⟩

  have hker_toZMod : ∀ c : ℤ_[q], PadicInt.toZMod c = 0 ↔ ∃ c', c = q * c' := by
    intro c
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c', rfl⟩; exact ⟨c', mul_comm _ _⟩
    · rintro ⟨c', rfl⟩; exact ⟨c', mul_comm _ _⟩
  have hred_ker : ∀ c : Δ × ι →₀ ℤ_[q], red c = 0 ↔ ∃ c', c = q • c' := by
    intro c
    rw [hred]
    constructor
    · intro h'
      have hc : ∀ τ, ∃ c', c τ = q * c' := fun τ => by
        rw [← hker_toZMod]
        have := DFunLike.congr_fun h' τ
        exact this
      choose g hg using hc
      refine ⟨Finsupp.onFinset c.support g (fun τ hτ => ?_), ?_⟩
      · rw [Finsupp.mem_support_iff]
        intro h0
        have := hg τ
        rw [h0] at this
        exact hτ ((mul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast (Fact.out : q.Prime).ne_zero))
      · ext τ
        simp [hg τ, nsmul_eq_mul]
    · rintro ⟨c', rfl⟩
      ext x
      rw [Finsupp.mapRange_apply, Finsupp.smul_apply, nsmul_eq_mul, (hker_toZMod _).mpr ⟨_, rfl⟩, Finsupp.coe_zero,
        Pi.zero_apply]
  have hkerΛ : ∀ x : Λ, πΛ x = 0 ↔ ∃ y : Λ, q • y = x := by
    intro x
    rw [hπΛ_apply, hred_ker]
    constructor
    · rintro ⟨c', hc'⟩
      obtain ⟨y, hy⟩ := htoS_surj (bS.repr.symm c')
      refine ⟨y, htoS_inj ?_⟩
      rw [map_nsmul, hy]
      apply bS.repr.injective
      rw [map_nsmul, LinearEquiv.apply_symm_apply, hc']
    · rintro ⟨y, rfl⟩
      exact ⟨bS.repr (toS y), by rw [map_nsmul, map_nsmul]⟩

  have htoS_act : ∀ (d : Δ) (x : Λ), toS ⟨actR d x, hΛ d x x.2⟩ = σS d (toS x) := fun _ _ => rfl
  have hπΛΔ : ∀ (d : Δ) (x : Λ), πΛ ⟨actR d x, hΛ d x x.2⟩ = PΛ d (πΛ x) := by
    intro d x
    rw [hπΛ_apply, hπΛ_apply, htoS_act, hrepr, hPΛ, hred, hred,
      Finsupp.mapDomain_mapRange _ _ _ _ (fun a b => map_add _ a b)]

  have key := IsLocalRing.finrank_invariants_linHom_fieldUnits_modPow_eq hΔ hqF actF (Rw q Kw) actR
    (fun d x => rfl) hspan (show e < e + 1 by omega) hfin (hpowall (e + 1) (by omega))
    (hnotorsall (e + 1) (by omega)) hidxm hidxme Λ hΛ PΛ πΛ hπΛ_surj hkerΛ hπΛΔ b hb N
    v hv hvker (fun d x => hvΔ (act d) x) PF πF hπF hkerπF (fun d u => hπFΔ d u) TF ιF hιF hranιF (fun d u => hιFΔ d u)
  exact key

end S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis
end P2MW
export P2MW.S_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_Kw_of_basis (solution)
