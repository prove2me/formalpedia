-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1592cbc3-36ee-53dc-8ff9-59a88e711d68

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem

set_option autoImplicit false

open CerednikDrinfeld.SpecialFormal.ModuliPackage

theorem solution
    {O : Type} [CommRing O] {k : Type} [Field k]
    {B B' : Type} [CommRing B] [CommRing B'] (ψ' : O →+* B')
    (φ : B' →+* B) (hφ : Function.Surjective φ)
    (ρ' : B' →+* k) (hρ' : Function.Surjective ρ')
    (t : B') (ht : t ≠ 0) (hker : RingHom.ker φ = Ideal.span {t}) (htm : t ∈ RingHom.ker ρ')
    (hann : ∀ m ∈ RingHom.ker ρ', m * t = 0)
    (hfst : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) = ρ'.comp ψ') :
    ∃ e : pullbackRing φ φ ≃+* pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom,
      (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom).comp e.toRingHom = pullbackFst φ φ ∧
      e.toRingHom.comp (pullbackStr φ φ ψ' ψ' rfl) =
        pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm ∧
      ((pullbackSnd φ φ).comp e.symm.toRingHom).comp
        (pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm) = ψ' := by
  classical

  set π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom with hπ

  have hW : ∀ c c' : B', c * t = c' * t → ρ' c = ρ' c' := by
    intro c c' hcc
    have h0 : (c - c') * t = 0 := by rw [sub_mul, hcc, sub_self]
    by_contra hne
    have hnot : c - c' ∉ RingHom.ker ρ' := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]; exact hne
    obtain ⟨y, m, hm, hym⟩ := (RingHom.ker_isMaximal_of_surjective ρ' hρ').exists_inv hnot
    apply ht
    calc t = (y * (c - c') + m) * t := by rw [hym, one_mul]
      _ = 0 := by rw [add_mul, mul_assoc, h0, mul_zero, zero_add, hann m hm]
  have hmemP : ∀ x : pullbackRing φ φ, φ x.1.1 = φ x.1.2 := fun x => x.2
  have hex : ∀ x : pullbackRing φ φ, ∃ c : B', c * t = x.1.2 - x.1.1 := by
    intro x
    have : x.1.2 - x.1.1 ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]; exact (hmemP x).symm
    rw [hker, Ideal.mem_span_singleton'] at this
    exact this
  choose cf hcf using hex

  have hρt : ∀ x : pullbackRing φ φ, ρ' x.1.2 = ρ' x.1.1 := by
    intro x
    have : ρ' (x.1.2 - x.1.1) = 0 := by rw [← hcf x, map_mul, show ρ' t = 0 from htm, mul_zero]
    rwa [map_sub, sub_eq_zero] at this

  let f₀ : pullbackRing φ φ → pullbackRing ρ' π := fun x =>
    ⟨(x.1.1, TrivSqZeroExt.inl (ρ' x.1.1) + TrivSqZeroExt.inr (ρ' (cf x))), by
      show ρ' x.1.1 = π (TrivSqZeroExt.inl (ρ' x.1.1) + TrivSqZeroExt.inr (ρ' (cf x)))
      simp [hπ]⟩
  have f₀_fst : ∀ x, (f₀ x).1.1 = x.1.1 := fun x => rfl
  have f₀_snd_fst : ∀ x, (f₀ x).1.2.fst = ρ' x.1.1 := fun x => by simp [f₀]
  have f₀_snd_snd : ∀ x, (f₀ x).1.2.snd = ρ' (cf x) := fun x => by simp [f₀]

  have extP : ∀ y y' : pullbackRing ρ' π, y.1.1 = y'.1.1 → y.1.2.fst = y'.1.2.fst → y.1.2.snd = y'.1.2.snd → y = y' := by
    intro y y' h1 h2 h3
    exact Subtype.ext (Prod.ext h1 (TrivSqZeroExt.ext h2 h3))
  let f : pullbackRing φ φ →+* pullbackRing ρ' π :=
    { toFun := f₀
      map_one' := by
        apply extP
        · rfl
        · rw [f₀_snd_fst]; show ρ' 1 = (1 : DualNumber k).fst; simp
        · rw [f₀_snd_snd]; show ρ' (cf 1) = (1 : DualNumber k).snd
          rw [TrivSqZeroExt.snd_one, hW (cf 1) 0 (by rw [hcf, zero_mul]; show (1 : B') - 1 = 0; simp)]
          simp
      map_mul' := by
        intro x y
        apply extP
        · rfl
        · rw [f₀_snd_fst]; show ρ' (x.1.1 * y.1.1) = ((f₀ x).1.2 * (f₀ y).1.2).fst
          rw [TrivSqZeroExt.fst_mul, f₀_snd_fst, f₀_snd_fst, map_mul]
        · rw [f₀_snd_snd]; show ρ' (cf (x * y)) = ((f₀ x).1.2 * (f₀ y).1.2).snd
          rw [TrivSqZeroExt.snd_mul, f₀_snd_fst, f₀_snd_fst, f₀_snd_snd, f₀_snd_snd]
          have : cf (x * y) * t = (cf x * y.1.2 + x.1.1 * cf y) * t := by
            rw [hcf, add_mul, mul_assoc, mul_comm y.1.2 t, ← mul_assoc, hcf, mul_assoc, hcf]
            show x.1.2 * y.1.2 - x.1.1 * y.1.1 = _
            ring
          rw [hW _ _ this, map_add, map_mul, map_mul, hρt y]
          simp [smul_eq_mul]
          ring
      map_zero' := by
        apply extP
        · rfl
        · rw [f₀_snd_fst]; show ρ' 0 = (0 : DualNumber k).fst; simp
        · rw [f₀_snd_snd]; show ρ' (cf 0) = (0 : DualNumber k).snd
          rw [TrivSqZeroExt.snd_zero, hW (cf 0) 0 (by rw [hcf, zero_mul]; show (0 : B') - 0 = 0; simp), map_zero]
      map_add' := by
        intro x y
        apply extP
        · rfl
        · rw [f₀_snd_fst]; show ρ' (x.1.1 + y.1.1) = ((f₀ x).1.2 + (f₀ y).1.2).fst
          rw [TrivSqZeroExt.fst_add, f₀_snd_fst, f₀_snd_fst, map_add]
        · rw [f₀_snd_snd]; show ρ' (cf (x + y)) = ((f₀ x).1.2 + (f₀ y).1.2).snd
          rw [TrivSqZeroExt.snd_add, f₀_snd_snd, f₀_snd_snd, ← map_add]
          apply hW
          rw [hcf, add_mul, hcf, hcf]
          show x.1.2 + y.1.2 - (x.1.1 + y.1.1) = _
          ring }

  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : x.1.1 = y.1.1 := by
      have := congrArg (fun z : pullbackRing ρ' π => z.1.1) hxy; exact this
    have h2 : ρ' (cf x) = ρ' (cf y) := by
      have := congrArg (fun z : pullbackRing ρ' π => z.1.2.snd) hxy
      simpa [f, f₀] using this
    have h3 : (cf x - cf y) * t = 0 := by
      apply hann; rw [RingHom.mem_ker, map_sub, h2, sub_self]
    apply Subtype.ext; apply Prod.ext h1
    have := hcf x; have := hcf y
    have : x.1.2 - x.1.1 = y.1.2 - y.1.1 := by
      rw [← hcf x, ← hcf y, ← sub_eq_zero, ← sub_mul, h3]
    rw [h1] at this
    exact sub_left_inj.mp this
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨c, hc⟩ := hρ' y.1.2.snd
    have hmem : (y.1.1, y.1.1 + c * t) ∈ pullbackRing φ φ := by
      show φ y.1.1 = φ (y.1.1 + c * t)
      rw [map_add, show φ (c * t) = 0 from ?_, add_zero]
      rw [← RingHom.mem_ker, hker]; exact Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self t)
    refine ⟨⟨(y.1.1, y.1.1 + c * t), hmem⟩, ?_⟩
    apply extP
    · rfl
    · show (f₀ ⟨(y.1.1, y.1.1 + c * t), hmem⟩).1.2.fst = _
      rw [f₀_snd_fst]; exact y.2
    · show (f₀ ⟨(y.1.1, y.1.1 + c * t), hmem⟩).1.2.snd = _
      rw [f₀_snd_snd, ← hc]; apply hW; rw [hcf]; show y.1.1 + c * t - y.1.1 = c * t; ring
  let e : pullbackRing φ φ ≃+* pullbackRing ρ' π := RingEquiv.ofBijective f ⟨hinj, hsurj⟩

  have heStr : e.toRingHom.comp (pullbackStr φ φ ψ' ψ' rfl) =
      pullbackStr ρ' π ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm := by
    apply RingHom.ext; intro o
    apply extP
    · rfl
    · show (f₀ (pullbackStr φ φ ψ' ψ' rfl o)).1.2.fst = (algebraMap k (DualNumber k) (ρ' (ψ' o))).fst
      rw [f₀_snd_fst, TrivSqZeroExt.algebraMap_eq_inl]; rfl
    · show (f₀ (pullbackStr φ φ ψ' ψ' rfl o)).1.2.snd = (algebraMap k (DualNumber k) (ρ' (ψ' o))).snd
      rw [f₀_snd_snd, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl,
        hW _ 0 (by rw [hcf, zero_mul]; show ψ' o - ψ' o = 0; simp), map_zero]
  refine ⟨e, RingHom.ext fun x => rfl, heStr, ?_⟩
  apply RingHom.ext; intro o
  show pullbackSnd φ φ (e.symm (pullbackStr ρ' π ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm o)) = ψ' o
  have : pullbackStr ρ' π ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm o = e (pullbackStr φ φ ψ' ψ' rfl o) :=
    (congrArg (fun g : O →+* _ => g o) heStr).symm
  rw [this, e.symm_apply_apply]
  rfl

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_ringEquiv_pullbackRing_self_dualNumber_of_span_singleton_of_mem (solution)
