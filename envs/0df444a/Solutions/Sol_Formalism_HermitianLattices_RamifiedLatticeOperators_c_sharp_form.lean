-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.c_sharp_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:03:27.268043+00:00
-- url     : https://prove2.me/submissions/33110c0e-9eb1-40f6-87a3-e268919d59bc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.OneDimInversion
open Finset Formalism.LogVandermondeBounds.product_first_zeroth_parts
section T1
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {R : Type} [CommRing R]
end T1
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
section Orb
end Orb
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.OneDimInversion
private lemma len_quot_pi {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) (ι : Type) [Fintype ι] (deg : ι → ℕ) :
    Module.length R ((ι → R) ⧸
      (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
      ((∑ i, deg i : ℕ) : ℕ∞) := by
  classical
  rw [(Submodule.quotientPi (fun i => (Ideal.span {ϖ ^ deg i} : Submodule R R))).length_eq,
    Module.length_pi_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R (deg i)
private lemma len_free_quot {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) (N : Type) [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] (e : ℕ) (K0 : Submodule R N) (hK0 : ∀ x : N, ϖ ^ e • x ∈ K0) :
    Module.length R (N ⧸ K0) ≤ ((e * Module.finrank R N : ℕ) : ℕ∞) := by
  classical
  let bs := Module.Free.chooseBasis R N
  let Kpi : Submodule R (Module.Free.ChooseBasisIndex R N → R) :=
    Submodule.pi Set.univ (fun _ => Ideal.span {ϖ ^ e})
  let f : (Module.Free.ChooseBasisIndex R N → R) →ₗ[R] N ⧸ K0 :=
    K0.mkQ ∘ₗ (bs.equivFun.symm : (Module.Free.ChooseBasisIndex R N → R) →ₗ[R] N)
  have hker : Kpi ≤ LinearMap.ker f := by
    intro v hv
    have hv' : ∀ i, ∃ c : R, c * ϖ ^ e = v i := fun i =>
      Ideal.mem_span_singleton'.1 ((Submodule.mem_pi.1 hv) i (Set.mem_univ i))
    choose c hc using hv'
    have hvc : v = ϖ ^ e • c := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hc i, mul_comm]
    rw [LinearMap.mem_ker, hvc, LinearMap.map_smul]
    show ϖ ^ e • K0.mkQ (bs.equivFun.symm c) = 0
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hK0 _
  let g := Kpi.liftQ f hker
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨n, rfl⟩ := K0.mkQ_surjective t
    refine ⟨Kpi.mkQ (bs.equivFun n), ?_⟩
    simp [g, f]
  calc Module.length R (N ⧸ K0)
      ≤ Module.length R ((Module.Free.ChooseBasisIndex R N → R) ⧸ Kpi) :=
        Module.length_le_of_surjective g hg
    _ = ((∑ _i : Module.Free.ChooseBasisIndex R N, e : ℕ) : ℕ∞) := len_quot_pi ϖ hϖ _ (fun _ => e)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Module.finrank_eq_card_chooseBasisIndex, mul_comm]
private lemma sat_pow {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ϖ : R)
    (P : Submodule R M) (h : ∀ x : M, ϖ • x ∈ P → x ∈ P) :
    ∀ (k : ℕ) (x : M), ϖ ^ k • x ∈ P → x ∈ P := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    apply h
    apply ih
    rwa [← mul_smul, ← pow_succ]
end Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
end Formalism.HermitianLattices.RamifiedLatticeOperators
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators
open Formalism.HermitianLattices.OneDimInversion
namespace Formalism.HermitianLattices.RamifiedLatticeOperators
theorem _root_.solution : LemmaC_sharp := by
  intro R _ _ _ ϖ hϖ M _ _ P S B U D e b hSB hBU hSD hPU hPD hsat hUD hfree hfin
  classical
  haveI := hfree
  haveI := hfin
  have hNS : S ⊓ P ≤ S := inf_le_left
  haveI : Module.Free R (S ⊓ P : Submodule R M) :=
    Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe hNS)
  haveI : Module.Finite R (S ⊓ P : Submodule R M) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hNS)
  set N : Submodule R M := S ⊓ P with hN
  set K1 : Submodule R N := (N.map ((ϖ ^ b) • U)).comap N.subtype with hK1
  set Sb : Submodule R B :=
    (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype with hSb
  let BP : Submodule R M := B ⊓ P
  have hu : ∀ x : BP, U x ∈ N := fun x =>
    Submodule.mem_inf.2 ⟨hBU (Submodule.mem_map_of_mem (Submodule.mem_inf.1 x.2).1),
      hPU (Submodule.mem_map_of_mem (Submodule.mem_inf.1 x.2).2)⟩
  let u : BP →ₗ[R] N := LinearMap.codRestrict N (U ∘ₗ BP.subtype) hu
  have hu_apply : ∀ x : BP, ((u x : N) : M) = U x := fun x => rfl
  let ψ0 : BP →ₗ[R] (N ⧸ K1) := K1.mkQ ∘ₗ u
  let L : Submodule R BP := (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap BP.subtype
  have hL : L ≤ LinearMap.ker ψ0 := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hx)
    have hsx' : ϖ ^ b • s = (x : M) := by simpa using hsx
    have hsP : s ∈ P := sat_pow ϖ P hsat b s (by rw [hsx']; exact (Submodule.mem_inf.1 x.2).2)
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hK1, Submodule.mem_comap]
    refine Submodule.mem_map.2 ⟨s, Submodule.mem_inf.2 ⟨hs, hsP⟩, ?_⟩
    rw [Submodule.subtype_apply, hu_apply, ← hsx', LinearMap.map_smul, LinearMap.smul_apply]
  let ψ : (BP ⧸ L) →ₗ[R] (N ⧸ K1) := L.liftQ ψ0 hL
  let W : Submodule R (N ⧸ K1) := LinearMap.range ψ
  have hadd := Module.length_eq_add_of_exact W.subtype W.mkQ Subtype.val_injective
    W.mkQ_surjective (LinearMap.exact_subtype_mkQ W)
  have hW : Module.length R W ≤ Module.length R (BP ⧸ L) :=
    Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
  have hle : L ≤ Sb.comap (Submodule.inclusion (inf_le_left : BP ≤ B)) := fun x hx => hx
  have hinj : Function.Injective (L.mapQ Sb (Submodule.inclusion (inf_le_left : BP ≤ B)) hle) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    have : Sb.comap (Submodule.inclusion (inf_le_left : BP ≤ B)) = L := by
      ext x
      rfl
    rw [this, Submodule.mkQ_map_self]
  have hBP : Module.length R (BP ⧸ L) ≤ Module.length R (B ⧸ Sb) :=
    Module.length_le_of_injective _ hinj
  let K0 : Submodule R N := LinearMap.range ((ϖ ^ e) • (LinearMap.id : N →ₗ[R] N))
  have hK0 : ∀ x : N, ϖ ^ e • x ∈ K0 := fun x => ⟨x, by simp⟩
  have hK0ker : K0 ≤ LinearMap.ker (W.mkQ ∘ₗ K1.mkQ) := by
    rintro _ ⟨n, rfl⟩
    have hnS : (n : M) ∈ S := (Submodule.mem_inf.1 n.2).1
    have hnP : (n : M) ∈ P := (Submodule.mem_inf.1 n.2).2
    have hDn : D n ∈ BP :=
      Submodule.mem_inf.2 ⟨hSD (Submodule.mem_map_of_mem hnS), hPD (Submodule.mem_map_of_mem hnP)⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨L.mkQ ⟨D n, hDn⟩, ?_⟩
    show ψ0 ⟨D n, hDn⟩ = _
    show K1.mkQ (u ⟨D n, hDn⟩) = _
    congr 1
    apply Subtype.ext
    rw [hu_apply]
    simp [hUD n n.2]
  have hQ : Module.length R ((N ⧸ K1) ⧸ W) ≤ Module.length R (N ⧸ K0) := by
    refine Module.length_le_of_surjective (K0.liftQ (W.mkQ ∘ₗ K1.mkQ) hK0ker) ?_
    intro t
    obtain ⟨t', rfl⟩ := W.mkQ_surjective t
    obtain ⟨n, rfl⟩ := K1.mkQ_surjective t'
    exact ⟨K0.mkQ n, rfl⟩
  have hfr := len_free_quot ϖ hϖ N e K0 hK0
  rw [hadd]
  exact add_le_add (hW.trans hBP) (hQ.trans hfr)
end Formalism.HermitianLattices.RamifiedLatticeOperators
