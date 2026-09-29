-- Prove2me | solution 1 for Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fd8b0765-a005-51f4-a55f-0f9e570bfb3f

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_Deformation_exists_wittVector_ghostComponent_truncate_map_mem_wittHom_fontaineKer_of_mvFormalGroup
import Theorems.Thm_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
import Theorems.Thm_MvFormalGroup_Points_exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v w

namespace S17H

section Plumbing

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)

theorem includeRight_surjective [Algebra 𝓞 (ZMod p)] (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] :
    Function.Surjective (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y) := by
  intro z
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective 𝓞 Y (ZMod p)
    (ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p))) z
  exact ⟨y, hy⟩

theorem includeRight_natCast_mul [Algebra 𝓞 (ZMod p)] {Y : Type w} [CommRing Y] [Algebra 𝓞 Y] (y : Y) :
    (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y) ((p : Y) * y) = 0 := by
  rw [map_mul, map_natCast]
  have : ((p : ℕ) : TensorProduct 𝓞 (ZMod p) Y) = algebraMap (ZMod p) _ (p : ZMod p) := by
    rw [map_natCast]
  rw [this, ZMod.natCast_self, map_zero, zero_mul]

theorem includeRight_eq_zero_of_mem [Algebra 𝓞 (ZMod p)] {Y : Type w} [CommRing Y] [Algebra 𝓞 Y] {y : Y}
    (hy : y ∈ Ideal.span {(p : Y)}) :
    (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y) y = 0 := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [mul_comm]; exact includeRight_natCast_mul p t

theorem mem_span_of_includeRight_eq_zero [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {Y : Type w} [CommRing Y] [Algebra 𝓞 Y] {y : Y}
    (hy : (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y) y = 0) :
    y ∈ Ideal.span {(p : Y)} := by

  have hsurj : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  let e : (𝓞 ⧸ RingHom.ker (algebraMap 𝓞 (ZMod p))) ≃ₐ[𝓞] ZMod p :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId 𝓞 (ZMod p)) hsurj
  let q : 𝓞 →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} :=
    (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : Y)})).comp (Algebra.ofId 𝓞 Y)
  have hq : ∀ a ∈ RingHom.ker (algebraMap 𝓞 (ZMod p)), q a = 0 := by
    intro a ha
    rw [hker] at ha
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    show Ideal.Quotient.mk _ (algebraMap 𝓞 Y (t * p)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  let f₀ : (𝓞 ⧸ RingHom.ker (algebraMap 𝓞 (ZMod p))) →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} :=
    Ideal.Quotient.liftₐ _ q hq
  let f : ZMod p →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} := f₀.comp (e.symm : ZMod p →ₐ[𝓞] _)
  let g : TensorProduct 𝓞 (ZMod p) Y →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} :=
    Algebra.TensorProduct.lift f (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : Y)})) (fun _ _ => Commute.all _ _)
  have hg : g (Algebra.TensorProduct.includeRight y) = Ideal.Quotient.mk (Ideal.span {(p : Y)}) y := by
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  rw [hy, map_zero] at hg
  exact Ideal.Quotient.eq_zero_iff_mem.1 hg.symm

theorem ker_includeRight_le [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] :
    RingHom.ker (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y).toRingHom ≤
      Ideal.span {(p : Y)} :=
  fun _ hy => mem_span_of_includeRight_eq_zero p hker hy

theorem ghostComponent_map [Fact p.Prime] {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (x : WittVector p R) (n : ℕ) :
    WittVector.ghostComponent n (WittVector.map f x) = f (WittVector.ghostComponent n x) := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, MvPolynomial.aeval_def,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem map_adicEval_eq_adicEval_bot {S : Type v} [CommRing S] [Algebra 𝓞 S]
    [IsAdicComplete (Ideal.span {(p : S)}) S] {S' : Type w} [CommRing S'] [Algebra 𝓞 S']
    (θ : S →ₐ[𝓞] S') (hθ : θ (p : S) ∈ (⊥ : Ideal S').radical) {d : ℕ} {x : Fin d → S}
    (hx : ∀ s, x s ∈ (Ideal.span {(p : S)}).radical) (G : MvPowerSeries (Fin d) 𝓞) :
    θ (MvFormalGroup.adicEval (Ideal.span {(p : S)}) x G) =
      MvFormalGroup.adicEval (⊥ : Ideal S') (fun s => θ (x s)) G := by
  refine MvFormalGroup.map_adicEval (Ideal.span {(p : S)}) ⊥ θ ⟨{(p : S)}, by simp⟩ ?_ hx G
  intro s hs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ hθ

theorem natCast_mem_radical_bot [Fact p.Prime] [Algebra 𝓞 (ZMod p)] (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] :
    ((p : ℕ) : TensorProduct 𝓞 (ZMod p) Y) ∈ (⊥ : Ideal (TensorProduct 𝓞 (ZMod p) Y)).radical := by
  refine ⟨1, ?_⟩
  rw [pow_one, Ideal.mem_bot]
  have : ((p : ℕ) : TensorProduct 𝓞 (ZMod p) Y) = algebraMap (ZMod p) _ (p : ZMod p) := by rw [map_natCast]
  rw [this, ZMod.natCast_self, map_zero]

theorem exists_eq_p_mul' {Y : Type w} [CommRing Y] {a : Y} (ha : a ∈ Ideal.span {(p : Y)}) :
    ∃ t : Y, a = (p : Y) * t := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ha
  exact ⟨t, by rw [← ht, mul_comm]⟩

theorem eq_of_pin (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {d : ℕ} (N : ℕ) (φi : MvPowerSeries (Fin d) 𝓞)
    (G G' : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * φi.coeff m) ∧
      (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = φi.coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m)))
    (hG' : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → G'.coeff m = (p : 𝓞) ^ (N - m.degree) * φi.coeff m) ∧
      (N < m.degree → G'.coeff m * (p : 𝓞) ^ (m.degree - N) = φi.coeff m ∨
        (G'.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m))) :
    G = G' := by
  ext m
  by_cases hm : m.degree ≤ N
  · rw [(hG m).1 hm, (hG' m).1 hm]
  · rw [not_le] at hm
    have hreg : (p : 𝓞) ^ (m.degree - N) ∈ nonZeroDivisors 𝓞 := pow_mem hp _
    rcases (hG m).2 hm with h1 | ⟨h1, h1'⟩ <;> rcases (hG' m).2 hm with h2 | ⟨h2, h2'⟩
    · exact (mul_cancel_right_mem_nonZeroDivisors hreg).1 (h1.trans h2.symm)
    · exact (h2' ⟨G.coeff m, by rw [← h1, mul_comm]⟩).elim
    · exact (h1' ⟨G'.coeff m, by rw [← h2, mul_comm]⟩).elim
    · rw [h1, h2]

end Plumbing

section Main

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hψT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
    (v : ℕ) (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R)))
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (χ : TensorProduct 𝓞 (ZMod p) R →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) R)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) R)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight :
              R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom
            (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) R)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y).toRingHom)

local notation "Rk" => TensorProduct 𝓞 (ZMod p) R
local notation "Yk" => TensorProduct 𝓞 (ZMod p) Y
local notation "inclR" => (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R)
local notation "inclY" => (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y)

include hp hker hFp hFp0 hφ0 hψ0 hφ1 hφT hψT hφF hψφ hφψ hπ hπX hπeval hkerπ hπΔ hunip hχ in
theorem main : ∃ x : R →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) x = χ := by
  classical

  haveI hYc : IsAdicComplete (Ideal.span {(p : Y)}) Y :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p Y

  have hsurjY := includeRight_surjective (𝓞 := 𝓞) p Y
  choose ŷ hŷ using fun i => hsurjY (χ (inclR (π (X i))))

  let χR : R →ₐ[𝓞] Yk := (χ.restrictScalars 𝓞).comp inclR
  have hχR : ∀ r, χR r = χ (inclR r) := fun r => rfl

  have hbridgeR : ∀ G : MvPowerSeries (Fin d) 𝓞,
      χ (inclR (π G)) = MvFormalGroup.adicEval (⊥ : Ideal Yk) (fun i => inclY (ŷ i)) G := by
    intro G
    rw [← hχR, hπeval, map_adicEval_eq_adicEval_bot p χR ?_ hπX G]
    · congr 1
      funext i
      rw [hχR, hŷ]
    · rw [map_natCast]
      exact natCast_mem_radical_bot (𝓞 := 𝓞) p Y

  have hŷrad : ∀ i, ŷ i ∈ (Ideal.span {(p : Y)}).radical := by
    intro i
    obtain ⟨k, hk⟩ := hπX i
    refine ⟨k, mem_span_of_includeRight_eq_zero p hker ?_⟩
    rw [map_pow, hŷ, ← map_pow, ← map_pow]
    exact (congrArg χ (includeRight_eq_zero_of_mem p hk)).trans (map_zero χ)
  have hbridge : ∀ G : MvPowerSeries (Fin d) 𝓞,
      χ (inclR (π G)) = inclY (MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ G) := by
    intro G
    rw [hbridgeR, map_adicEval_eq_adicEval_bot p inclY (by rw [map_natCast]; exact natCast_mem_radical_bot (𝓞 := 𝓞) p Y) hŷrad G]

  let y : MvFormalGroup.Points F Y (Ideal.span {(p : Y)}) := ⟨ŷ, hŷrad⟩
  have hw : ∀ j, MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ (F.nthSeries (p ^ v) j) ∈ Ideal.span {(p : Y)} := by
    intro j
    apply mem_span_of_includeRight_eq_zero p hker
    rw [← hbridge]
    have : π (F.nthSeries (p ^ v) j) = 0 := by
      rw [← RingHom.mem_ker, hkerπ]
      exact Ideal.subset_span ⟨j, rfl⟩
    rw [this, map_zero, map_zero]
  choose w' hw' using fun j => exists_eq_p_mul' p (hw j)

  obtain ⟨N₀, hN₀⟩ :=
    Deformation.exists_wittVector_ghostComponent_truncate_map_mem_wittHom_fontaineKer_of_mvFormalGroup
      p hp hker F Fp hFp hFp0 φ hφ0 hφ1 hφT hφF v R π hπ hπX hπeval hkerπ hπΔ hunip
  let ev : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] Y := MvFormalGroup.adicEvalAlgHom (Ideal.span {(p : Y)}) hŷrad
  have hev : ∀ G, ev G = MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ G :=
    fun G => congrFun (MvFormalGroup.coe_adicEvalAlgHom (Ideal.span {(p : Y)}) hŷrad) G
  have hθ : (inclY).toRingHom.comp ev.toRingHom = χ.toRingHom.comp ((inclR).toRingHom.comp π.toRingHom) := by
    refine RingHom.ext fun G => ?_
    show inclY (ev G) = χ (inclR (π G))
    rw [hev, hbridge]
  have hGev : ∀ N : ℕ, N₀ ≤ N → ∀ (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
        (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
          (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
      MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ G ∈ Ideal.span {(p : Y) ^ N} := by
    intro N hN i G hGpin
    obtain ⟨ℓ, hghost, hhom, hkerw⟩ := hN₀ N hN i
    have hGeq : G = WittVector.ghostComponent (N - 1) ℓ := eq_of_pin p hp N (φ i) G _ hGpin hghost
    let m : Deformation.wittHom (ZMod p) p N Rk :=
      ⟨WittVector.truncate N (WittVector.map ((inclR).toRingHom.comp π.toRingHom) ℓ), hhom⟩
    have h := hχ N m hkerw
    rw [Deformation.TruncWitt.mem_fontaineKer_iff] at h
    obtain ⟨Z, hZ, hZg⟩ := h

    have hT : WittVector.truncate N (WittVector.map (inclY).toRingHom (WittVector.map ev.toRingHom ℓ)) =
        WittVector.truncate N (WittVector.map (inclY).toRingHom Z) := by
      rw [hZ]
      show _ = Deformation.TruncWitt.map χ.toRingHom
        (WittVector.truncate N (WittVector.map ((inclR).toRingHom.comp π.toRingHom) ℓ))
      rw [Deformation.TruncWitt.map_truncate]
      congr 1
      ext k
      simp only [WittVector.map_coeff, RingHom.comp_apply]
      exact (RingHom.congr_fun hθ (ℓ.coeff k))
    have hind := Deformation.TruncWitt.ghostComponent_pred_mem_of_truncate_map_eq
      (ker_includeRight_le p hker Y) hT hZg
    rwa [ghostComponent_map, ← hGeq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hev] at hind

  obtain ⟨n₀, hn₀⟩ := MvFormalGroup.eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
    p hp F Fp hFp hFp0 φ hφ0 hφT hφF
    (fun i j m => MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
      p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF i j m)
    v Y ŷ hŷrad w' hw' ⟨N₀, hGev⟩

  have hwy : ∀ i, (p ^ v • y).val i = (p : Y) * w' i := by
    intro i
    rw [MvFormalGroup.Points.val_nsmul]
    exact hw' i
  obtain ⟨y', hy'0, hy'⟩ :=
    (MvFormalGroup.Points.exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog p hp F Fp hFp hFp0 φ ψ hφ0 hψ0
      hφ1 hφT hψT hφF hψφ hφψ Y y v w' hwy).2 ⟨n₀, hn₀⟩

  let ev' : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] Y := MvFormalGroup.adicEvalAlgHom (Ideal.span {(p : Y)}) y'.mem_radical
  have hev' : ∀ G, ev' G = MvFormalGroup.adicEval (Ideal.span {(p : Y)}) y'.val G :=
    fun G => congrFun (MvFormalGroup.coe_adicEvalAlgHom (Ideal.span {(p : Y)}) y'.mem_radical) G
  have hkill : ∀ a ∈ RingHom.ker π, ev' a = 0 := by
    rw [hkerπ]
    intro a ha
    refine Submodule.span_induction ?_ (map_zero _) (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero])
      (fun c a _ ha => by rw [smul_eq_mul, map_mul, ha, mul_zero]) ha
    rintro _ ⟨j, rfl⟩
    rw [hev']
    have := congrFun (MvFormalGroup.Points.val_nsmul (p ^ v) y') j
    rw [hy'0, MvFormalGroup.Points.val_zero] at this
    exact this.symm
  let e : (MvPowerSeries (Fin d) 𝓞 ⧸ RingHom.ker π) ≃ₐ[𝓞] R := Ideal.quotientKerAlgEquivOfSurjective hπ
  let x : R →ₐ[𝓞] Y := (Ideal.Quotient.liftₐ (RingHom.ker π) ev' hkill).comp (e.symm : R →ₐ[𝓞] _)
  have hx : ∀ G, x (π G) = ev' G := by
    intro G
    show Ideal.Quotient.liftₐ (RingHom.ker π) ev' hkill (e.symm (π G)) = ev' G
    have : e.symm (π G) = Ideal.Quotient.mk (RingHom.ker π) G := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl

  refine ⟨x, ?_⟩
  have hred : (fun i => inclY (y'.val i)) = fun i => inclY (ŷ i) := by
    funext i
    have h1 := hy' i
    have : y'.val i = ŷ i + (y'.val i - ŷ i) := by ring
    rw [this, map_add, includeRight_eq_zero_of_mem p h1, add_zero]
  have key : ∀ r : R, inclY (x r) = χ (inclR r) := by
    intro r
    obtain ⟨G, rfl⟩ := hπ r
    rw [hx, hev', map_adicEval_eq_adicEval_bot p inclY (by rw [map_natCast]; exact natCast_mem_radical_bot (𝓞 := 𝓞) p Y) y'.mem_radical G,
      hred, ← hbridgeR]
  refine Algebra.TensorProduct.ext' fun a r => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e1 : (a ⊗ₜ[𝓞] x r : Yk) = algebraMap (ZMod p) Yk a * inclY (x r) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_self, RingHom.id_apply]
  have e2 : (a ⊗ₜ[𝓞] r : Rk) = algebraMap (ZMod p) Rk a * inclR r := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_self, RingHom.id_apply]
  rw [e1, e2, map_mul, AlgHom.commutes, key]

end Main

end S17H

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]

    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hψT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)

    (v : ℕ) (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R)))

    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (χ : TensorProduct 𝓞 (ZMod p) R →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) R)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) R)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight :
              R →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom
            (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) R)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y).toRingHom) :
    ∃ x : R →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) x = χ :=
  S17H.main p hp hker F Fp hFp hFp0 φ ψ hφ0 hψ0 hφ1 hφT hψT hφF hψφ hφψ v R π hπ hπX hπeval hkerπ hπΔ hunip Y χ hχ

end S_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup
end P2MW
export P2MW.S_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup (solution)
