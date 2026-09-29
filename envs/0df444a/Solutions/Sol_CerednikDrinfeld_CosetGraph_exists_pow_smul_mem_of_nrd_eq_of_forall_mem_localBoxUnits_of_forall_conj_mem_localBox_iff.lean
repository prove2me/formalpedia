-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_pow_smul_mem_of_nrd_eq_of_forall_mem_localBoxUnits_of_forall_conj_mem_localBox_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/74097e6d-81dd-5652-b167-265fd75fe4fb

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_pow_smul_mem_of_nrd_eq_of_forall_mem_localBoxUnits_of_forall_conj_mem_localBox_iff
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace WIntegral

local notation "Kv" w => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w

variable {a b : ℚ}

theorem nrd_coords (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (⟨algebraMap ℚ (Kv w) z.re, algebraMap ℚ (Kv w) z.imI,
        algebraMap ℚ (Kv w) z.imJ, algebraMap ℚ (Kv w) z.imK⟩ :
          ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) =
      algebraMap ℚ (Kv w) (QuaternionAlgebra.nrd z) := by
  rw [QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_add, map_sub, map_mul, map_pow]

theorem tmul_one_mem_localBox_of_isMaximalOrder (w : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] Kv w, x ≠ 0 → IsUnit x)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (z : ℍ[ℚ, a, b]) (hz : algebraMap ℚ (Kv w) (QuaternionAlgebra.nrd z) ∈ w.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] (1 : Kv w) ∈ Submodule.localBox Λ w := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := Kv w) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (Kv w) a) (d₂ := (0 : Kv w)) (d₃ := algebraMap ℚ (Kv w) b) rfl (map_zero _) rfl
    (AlgEquiv.refl (R := Kv w) (A₁ := ℍ[Kv w, algebraMap ℚ (Kv w) a, (0 : Kv w), algebraMap ℚ (Kv w) b]))
  have hφ' : ∀ (x : ℍ[ℚ, a, b]) (r : Kv w),
      φ (x ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (Kv w) x.re, algebraMap ℚ (Kv w) x.imI,
        algebraMap ℚ (Kv w) x.imJ, algebraMap ℚ (Kv w) x.imK⟩ :
          ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) := fun x r => by
    rw [hφ]; rfl
  rw [QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ w hdiv
    φ hφ', hφ', one_smul, nrd_coords]
  exact hz

theorem tmul_one_mem_localBox_of_isEichlerOrder (w : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] Kv w, x ≠ 0 → IsUnit x)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (z : ℍ[ℚ, a, b]) (hz : algebraMap ℚ (Kv w) (QuaternionAlgebra.nrd z) ∈ w.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] (1 : Kv w) ∈ Submodule.localBox R w := by
  obtain ⟨Λ₁, Λ₂, h₁, h₂, rfl, -⟩ := hR
  rw [Submodule.localBox_inf Λ₁ Λ₂ h₁.isOrder.fg h₁.isOrder.spanTop h₂.isOrder.fg h₂.isOrder.spanTop w]
  exact ⟨tmul_one_mem_localBox_of_isMaximalOrder w hdiv h₁ z hz,
    tmul_one_mem_localBox_of_isMaximalOrder w hdiv h₂ z hz⟩

theorem coe_toLoc (w : HeightOneSpectrum (𝓞 ℚ)) (u : (ℍ[ℚ, a, b])ˣ) :
    ((CerednikDrinfeld.CosetGraph.toLoc w u : (CerednikDrinfeld.CosetGraph.Loc a b w)ˣ) :
        CerednikDrinfeld.CosetGraph.Loc a b w) = (u : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv w) := rfl

end WIntegral

open QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (wbar : (ℍ[ℚ, a, b])ˣ)
    (hnrd : QuaternionAlgebra.nrd (wbar : ℍ[ℚ, a, b]) = (q : ℚ))
    (hunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        CosetGraph.toLoc w wbar ∈ Submodule.localBoxUnits R w)
    (hnorm : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ x : CosetGraph.Loc a b w,
        ((((CosetGraph.toLoc w wbar)⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) * x *
            ((CosetGraph.toLoc w wbar : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox R w ↔
          x ∈ Submodule.localBox R w) ∧
        ((((CosetGraph.toLoc w wbar)⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) * x *
            ((CosetGraph.toLoc w wbar : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox Λ w ↔
          x ∈ Submodule.localBox Λ w)) :
    ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • ((wbar : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := by
  refine (QuaternionAlgebra.IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem R hR.isOrder r v hv
    (wbar : ℍ[ℚ, a, b])).mp fun w hwv => ?_
  by_cases hqw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  · refine WIntegral.tmul_one_mem_localBox_of_isEichlerOrder w ((hdef.2.2 w).mpr hqw) hR _ ?_
    rw [hnrd, map_natCast]
    exact natCast_mem _ q
  · have h := (hunit w hwv hqw).1
    rwa [WIntegral.coe_toLoc] at h

end S_CerednikDrinfeld_CosetGraph_exists_pow_smul_mem_of_nrd_eq_of_forall_mem_localBoxUnits_of_forall_conj_mem_localBox_iff
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_pow_smul_mem_of_nrd_eq_of_forall_mem_localBoxUnits_of_forall_conj_mem_localBox_iff (solution)
