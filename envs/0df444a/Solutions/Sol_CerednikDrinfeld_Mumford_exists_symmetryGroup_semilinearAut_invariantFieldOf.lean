-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.exists_symmetryGroup_semilinearAut_invariantFieldOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0d77b207-0560-5b9c-9170-8a7afca6ff26

import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_exists_symmetryGroup_semilinearAut_invariantFieldOf

set_option autoImplicit false

open CerednikDrinfeld.Mumford AlgebraicCurve

namespace TwistedActionBody

abbrev Z2 : Type := Multiplicative (ZMod 2)

def gen : Z2 := Multiplicative.ofAdd 1

theorem z2_cases (a : Z2) : a = 1 ∨ a = gen := by
  unfold gen; revert a; decide

theorem gen_ne_one : gen ≠ 1 := by unfold gen; decide

theorem gen_mul_gen : gen * gen = 1 := by unfold gen; decide

section Lift

variable {H : Type} [Group H]

def lift (h : H) (a : Z2) : H := if a = 1 then 1 else h

@[scoped simp] theorem lift_one (h : H) : lift h 1 = 1 := if_pos rfl

@[scoped simp] theorem lift_gen (h : H) : lift h gen = h := if_neg gen_ne_one

theorem lift_mul (h : H) (hh : h * h = 1) (a b : Z2) : lift h (a * b) = lift h a * lift h b := by
  rcases z2_cases a with rfl | rfl <;> rcases z2_cases b with rfl | rfl
  · rw [one_mul, lift_one, one_mul]
  · rw [one_mul, lift_one, one_mul]
  · rw [mul_one, lift_one, mul_one]
  · rw [gen_mul_gen, lift_one, lift_gen, hh]

theorem lift_comm (h : H) {k : H} (hk : h * k = k * h) (a : Z2) : lift h a * k = k * lift h a := by
  rcases z2_cases a with rfl | rfl
  · rw [lift_one, one_mul, mul_one]
  · rw [lift_gen, hk]

theorem comm_left {x y : H} (z : H) (h : x * y = y * x) : x * (y * z) = y * (x * z) := by
  rw [← mul_assoc, h, mul_assoc]

variable {D : Type} [Group D]

def liftAll (f : D →* H) (h₀ h₁ : H) (hh₀ : h₀ * h₀ = 1) (hh₁ : h₁ * h₁ = 1) (h01 : h₀ * h₁ = h₁ * h₀)
    (hf0 : ∀ τ, f τ * h₀ = h₀ * f τ) (hf1 : ∀ τ, f τ * h₁ = h₁ * f τ) : D × (Z2 × Z2) →* H where
  toFun σ := f σ.1 * (lift h₀ σ.2.1 * lift h₁ σ.2.2)
  map_one' := by simp
  map_mul' σ σ' := by
    obtain ⟨τ, a, b⟩ := σ
    obtain ⟨τ', a', b'⟩ := σ'
    show f (τ * τ') * (lift h₀ (a * a') * lift h₁ (b * b')) =
      f τ * (lift h₀ a * lift h₁ b) * (f τ' * (lift h₀ a' * lift h₁ b'))
    rw [map_mul, lift_mul h₀ hh₀, lift_mul h₁ hh₁]
    have c1 : lift h₁ b * f τ' = f τ' * lift h₁ b := lift_comm h₁ (hf1 τ').symm b
    have c2 : lift h₀ a * f τ' = f τ' * lift h₀ a := lift_comm h₀ (hf0 τ').symm a
    have c3 : lift h₁ b * lift h₀ a' = lift h₀ a' * lift h₁ b :=
      lift_comm h₁ (k := lift h₀ a') (lift_comm h₀ h01 a').symm b
    simp only [mul_assoc]
    rw [comm_left _ c1, comm_left _ c2, comm_left _ c3]

theorem liftAll_apply (f : D →* H) (h₀ h₁ : H) (hh₀ : h₀ * h₀ = 1) (hh₁ : h₁ * h₁ = 1) (h01 : h₀ * h₁ = h₁ * h₀)
    (hf0 : ∀ τ, f τ * h₀ = h₀ * f τ) (hf1 : ∀ τ, f τ * h₁ = h₁ * f τ) (σ : D × (Z2 × Z2)) :
    liftAll f h₀ h₁ hh₀ hh₁ h01 hf0 hf1 σ = f σ.1 * (lift h₀ σ.2.1 * lift h₁ σ.2.2) := rfl

end Lift

section Group

variable (D : Type) [Group D]

abbrev S : Type := D × (Z2 × Z2)

def ιS : D →* S D := MonoidHom.inl D (Z2 × Z2)
def scalar : S D →* D := MonoidHom.fst D (Z2 × Z2)
def σ₀ : S D := (1, (gen, 1))
def σ₁ : S D := (1, (1, gen))

@[scoped simp] theorem ιS_apply (τ : D) : ιS D τ = (τ, (1, 1)) := rfl
@[scoped simp] theorem scalar_apply (σ : S D) : scalar D σ = σ.1 := rfl

theorem scalar_ιS (τ : D) : scalar D (ιS D τ) = τ := rfl

theorem presentation (σ : S D) : ∃ (τ : D) (u v : ℕ), σ = ιS D τ * σ₀ D ^ u * σ₁ D ^ v := by
  obtain ⟨τ, a, b⟩ := σ
  rcases z2_cases a with rfl | rfl <;> rcases z2_cases b with rfl | rfl
  · exact ⟨τ, 0, 0, by simp⟩
  · exact ⟨τ, 0, 1, by simp [σ₁]⟩
  · exact ⟨τ, 1, 0, by simp [σ₀]⟩
  · exact ⟨τ, 1, 1, by simp [σ₀, σ₁]⟩

theorem relations :
    scalar D (σ₀ D) = 1 ∧ scalar D (σ₁ D) = 1 ∧ σ₀ D * σ₀ D = 1 ∧ σ₁ D * σ₁ D = 1 ∧
    σ₀ D * σ₁ D = σ₁ D * σ₀ D ∧ (∀ τ, ιS D τ * σ₀ D = σ₀ D * ιS D τ) ∧ (∀ τ, ιS D τ * σ₁ D = σ₁ D * ιS D τ) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [σ₀, Prod.ext_iff, gen_mul_gen]
  · simp [σ₁, Prod.ext_iff, gen_mul_gen]
  · simp [σ₀, σ₁]
  · intro τ; simp [σ₀]
  · intro τ; simp [σ₁]

theorem universal (H : Type) [Group H] (f : D →* H) (h₀ h₁ : H)
    (hh₀ : h₀ * h₀ = 1) (hh₁ : h₁ * h₁ = 1) (h01 : h₀ * h₁ = h₁ * h₀)
    (hf0 : ∀ τ, f τ * h₀ = h₀ * f τ) (hf1 : ∀ τ, f τ * h₁ = h₁ * f τ) :
    ∃ F : S D →* H, (∀ τ, F (ιS D τ) = f τ) ∧ F (σ₀ D) = h₀ ∧ F (σ₁ D) = h₁ :=
  ⟨liftAll f h₀ h₁ hh₀ hh₁ h01 hf0 hf1, fun τ => by simp [liftAll_apply], by simp [liftAll_apply, σ₀],
    by simp [liftAll_apply, σ₁]⟩

def χS (χ : D →* Z2) : S D →* Z2 :=
  (χ.comp (MonoidHom.fst D (Z2 × Z2))) * ((MonoidHom.fst Z2 Z2).comp (MonoidHom.snd D (Z2 × Z2)))

theorem χS_apply (χ : D →* Z2) (σ : S D) : χS D χ σ = χ σ.1 * σ.2.1 := rfl

theorem parity (χ : D →* Z2) : (∀ τ, χS D χ (ιS D τ) = χ τ) ∧ χS D χ (σ₀ D) ≠ 1 ∧ χS D χ (σ₁ D) = 1 := by
  refine ⟨fun τ => by rw [χS_apply, ιS_apply, mul_one], ?_, ?_⟩
  · rw [χS_apply]; show χ 1 * gen ≠ 1; rw [map_one, one_mul]; exact gen_ne_one
  · rw [χS_apply]; show χ 1 * 1 = 1; rw [map_one, one_mul]

end Group

section Action

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
variable (D : Type) [Group D] (amb : D →* AmbientSemilinearAut K G M) (χ : D →* Z2)
variable (Δ : Subgroup G)

noncomputable def θ (n : ↥(Subgroup.normalizer (Δ : Set G))) : ↥(SemilinearAut K ↥(invariantFieldOf K G M Δ)) :=
  SemilinearAut.ofAlgAut (normalizerAct K G M Δ n)

theorem θ_smul_coe (n : ↥(Subgroup.normalizer (Δ : Set G))) (y : ↥(invariantFieldOf K G M Δ)) :
    ((θ K G M Δ n • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = (n : G) • (y : FractionRing M) := rfl

theorem baseAut_θ (n : ↥(Subgroup.normalizer (Δ : Set G))) : SemilinearAut.baseAut (θ K G M Δ n) = 1 := rfl

theorem θ_mul (n n' : ↥(Subgroup.normalizer (Δ : Set G))) : θ K G M Δ n * θ K G M Δ n' = θ K G M Δ (n * n') := by
  unfold θ; rw [← map_mul, ← map_mul]

theorem θ_eq_one_of_forall (n : ↥(Subgroup.normalizer (Δ : Set G)))
    (h : ∀ x ∈ invariantFieldOf K G M Δ, (n : G) • x = x) : θ K G M Δ n = 1 := by
  have : normalizerAct K G M Δ n = 1 := AlgEquiv.ext fun x => Subtype.ext (h x x.2)
  unfold θ; rw [this, map_one]

theorem θ_eq_of_forall (n n' : ↥(Subgroup.normalizer (Δ : Set G)))
    (h : ∀ x ∈ invariantFieldOf K G M Δ, (n : G) • x = (n' : G) • x) : θ K G M Δ n = θ K G M Δ n' := by
  have : normalizerAct K G M Δ n = normalizerAct K G M Δ n' := AlgEquiv.ext fun x => Subtype.ext (h x x.2)
  unfold θ; rw [this]

noncomputable def C : D →* ↥(SemilinearAut K ↥(invariantFieldOf K G M Δ)) :=
  (AmbientSemilinearAut.coeffActOfHom Δ).comp amb

theorem C_apply (τ : D) : C K G M D amb Δ τ = AmbientSemilinearAut.coeffActOf Δ (amb τ) := rfl

theorem C_smul_coe (τ : D) (y : ↥(invariantFieldOf K G M Δ)) :
    ((C K G M D amb Δ τ • y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) =
      AmbientSemilinearAut.fracMap (amb τ) (y : FractionRing M) := rfl

theorem baseAut_C (τ : D) :
    SemilinearAut.baseAut (C K G M D amb Δ τ) = SemilinearAut.baseAut (AmbientSemilinearAut.coeffActOf Δ (amb τ)) := rfl

theorem θ_comm_C (n : ↥(Subgroup.normalizer (Δ : Set G))) (τ : D) :
    θ K G M Δ n * C K G M D amb Δ τ = C K G M D amb Δ τ * θ K G M Δ n := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact (coeffActOf_comm_normalizerAct K G M (amb τ) Δ n x).symm
  · show (1 : K ≃+* K) * SemilinearAut.baseAut (AmbientSemilinearAut.coeffActOf Δ (amb τ)) =
      SemilinearAut.baseAut (AmbientSemilinearAut.coeffActOf Δ (amb τ)) * 1
    rw [one_mul, mul_one]

variable (w : G) (hw : w ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))

noncomputable def fHom (hww : ∀ x ∈ invariantFieldOf K G M Δ, (w * w) • x = x) :
    D →* ↥(SemilinearAut K ↥(invariantFieldOf K G M Δ)) where
  toFun τ := lift (θ K G M Δ ⟨w, hw⟩) (χ τ) * C K G M D amb Δ τ
  map_one' := by rw [map_one, lift_one, map_one, one_mul]
  map_mul' τ τ' := by
    have hθθ : θ K G M Δ ⟨w, hw⟩ * θ K G M Δ ⟨w, hw⟩ = 1 := by
      rw [θ_mul]; exact θ_eq_one_of_forall K G M Δ _ hww
    rw [map_mul, lift_mul _ hθθ, map_mul]
    have c : lift (θ K G M Δ ⟨w, hw⟩) (χ τ') * C K G M D amb Δ τ = C K G M D amb Δ τ * lift (θ K G M Δ ⟨w, hw⟩) (χ τ') :=
      lift_comm _ (θ_comm_C K G M D amb Δ ⟨w, hw⟩ τ) (χ τ')
    simp only [mul_assoc]
    rw [comm_left _ c]

theorem fHom_apply (hww : ∀ x ∈ invariantFieldOf K G M Δ, (w * w) • x = x) (τ : D) :
    fHom K G M D amb χ Δ w hw hww τ = lift (θ K G M Δ ⟨w, hw⟩) (χ τ) * C K G M D amb Δ τ := rfl

end Action

end TwistedActionBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_Mumford_exists_symmetryGroup_semilinearAut_invariantFieldOf.TwistedActionBody"

open CerednikDrinfeld TwistedActionBody

theorem solution
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
    (D : Type) [Group D] (amb : D →* Mumford.AmbientSemilinearAut K G M) (χ : D →* Multiplicative (ZMod 2)) :
    ∃ (S : Type) (_ : Group S) (scalar : S →* D) (ιS : D →* S) (_ : ∀ τ, scalar (ιS τ) = τ) (σ₀ σ₁ : S)
      (χS : S →* Multiplicative (ZMod 2)),

      (∀ σ : S, ∃ (τ : D) (u v : ℕ), σ = ιS τ * σ₀ ^ u * σ₁ ^ v) ∧
      scalar σ₀ = 1 ∧ scalar σ₁ = 1 ∧ σ₀ * σ₀ = 1 ∧ σ₁ * σ₁ = 1 ∧
      σ₀ * σ₁ = σ₁ * σ₀ ∧ (∀ τ, ιS τ * σ₀ = σ₀ * ιS τ) ∧ (∀ τ, ιS τ * σ₁ = σ₁ * ιS τ) ∧

      (∀ (H : Type) [Group H] (f : D →* H) (h₀ h₁ : H),
        h₀ * h₀ = 1 → h₁ * h₁ = 1 → h₀ * h₁ = h₁ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₁ = h₁ * f τ) →
        ∃ F : S →* H, (∀ τ, F (ιS τ) = f τ) ∧ F σ₀ = h₀ ∧ F σ₁ = h₁) ∧

      (∀ τ, χS (ιS τ) = χ τ) ∧ χS σ₀ ≠ 1 ∧ χS σ₁ = 1 ∧

      ∀ (Δ : Subgroup G) (w wbar : G) (hw : w ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))
        (hwbar : wbar ∈ Subgroup.normalizer ((Δ : Subgroup G) : Set G))
        (hww : ∀ x ∈ Mumford.invariantFieldOf K G M Δ, (w * w) • x = x)
        (hbb : ∀ x ∈ Mumford.invariantFieldOf K G M Δ, (wbar * wbar) • x = x)
        (hwb : ∀ x ∈ Mumford.invariantFieldOf K G M Δ, (w * wbar) • x = (wbar * w) • x),
        ∃ galC : S →* AlgebraicCurve.SemilinearAut K ↥(Mumford.invariantFieldOf K G M Δ),
          (∀ (σ : S) (c : K), SemilinearAut.baseAut (galC σ) c =
            SemilinearAut.baseAut (Mumford.AmbientSemilinearAut.coeffActOf Δ (amb (scalar σ))) c) ∧
          (∀ (τ : D) (y : ↥(Mumford.invariantFieldOf K G M Δ)),
            ((galC (ιS τ) • y : ↥(Mumford.invariantFieldOf K G M Δ)) : FractionRing M) =
              (if χ τ = 1 then (1 : G) else w) • Mumford.AmbientSemilinearAut.fracMap (amb τ) (y : FractionRing M)) ∧
          (∀ y : ↥(Mumford.invariantFieldOf K G M Δ), ((galC σ₀ • y : ↥(Mumford.invariantFieldOf K G M Δ)) : FractionRing M) = w • (y : FractionRing M)) ∧
          (∀ y : ↥(Mumford.invariantFieldOf K G M Δ), ((galC σ₁ • y : ↥(Mumford.invariantFieldOf K G M Δ)) : FractionRing M) = wbar • (y : FractionRing M)) := by
  classical
  refine ⟨S D, inferInstance, scalar D, ιS D, scalar_ιS D, σ₀ D, σ₁ D, χS D χ, presentation D,
    (relations D).1, (relations D).2.1, (relations D).2.2.1, (relations D).2.2.2.1, (relations D).2.2.2.2.1,
    (relations D).2.2.2.2.2.1, (relations D).2.2.2.2.2.2, universal D, (parity D χ).1, (parity D χ).2.1, (parity D χ).2.2, ?_⟩
  intro Δ w wbar hw hwbar hww hbb hwb

  have hθw : θ K G M Δ ⟨w, hw⟩ * θ K G M Δ ⟨w, hw⟩ = 1 := by
    rw [θ_mul]; exact θ_eq_one_of_forall K G M Δ _ hww
  have hθb : θ K G M Δ ⟨wbar, hwbar⟩ * θ K G M Δ ⟨wbar, hwbar⟩ = 1 := by
    rw [θ_mul]; exact θ_eq_one_of_forall K G M Δ _ hbb
  have hθwb : θ K G M Δ ⟨w, hw⟩ * θ K G M Δ ⟨wbar, hwbar⟩ = θ K G M Δ ⟨wbar, hwbar⟩ * θ K G M Δ ⟨w, hw⟩ := by
    rw [θ_mul, θ_mul]; exact θ_eq_of_forall K G M Δ _ _ hwb
  have hf0 : ∀ τ, fHom K G M D amb χ Δ w hw hww τ * θ K G M Δ ⟨w, hw⟩ = θ K G M Δ ⟨w, hw⟩ * fHom K G M D amb χ Δ w hw hww τ := by
    intro τ
    rw [fHom_apply, mul_assoc, ← θ_comm_C, ← mul_assoc, lift_comm _ rfl (χ τ), mul_assoc]
  have hf1 : ∀ τ, fHom K G M D amb χ Δ w hw hww τ * θ K G M Δ ⟨wbar, hwbar⟩ = θ K G M Δ ⟨wbar, hwbar⟩ * fHom K G M D amb χ Δ w hw hww τ := by
    intro τ
    rw [fHom_apply, mul_assoc, ← θ_comm_C, ← mul_assoc, lift_comm _ hθwb (χ τ), mul_assoc]
  refine ⟨liftAll (fHom K G M D amb χ Δ w hw hww) (θ K G M Δ ⟨w, hw⟩) (θ K G M Δ ⟨wbar, hwbar⟩) hθw hθb hθwb hf0 hf1,
    ?_, ?_, ?_, ?_⟩
  ·
    intro σ c
    have hbl : ∀ a, SemilinearAut.baseAut (lift (θ K G M Δ ⟨w, hw⟩) a) = 1 := fun a => by
      rcases z2_cases a with rfl | rfl
      · rw [lift_one]; rfl
      · rw [lift_gen]; rfl
    have hbl' : ∀ a, SemilinearAut.baseAut (lift (θ K G M Δ ⟨wbar, hwbar⟩) a) = 1 := fun a => by
      rcases z2_cases a with rfl | rfl
      · rw [lift_one]; rfl
      · rw [lift_gen]; rfl
    rw [liftAll_apply, fHom_apply, SemilinearAut.baseAut_mul, SemilinearAut.baseAut_mul, SemilinearAut.baseAut_mul,
      hbl, hbl, hbl', one_mul, mul_one, mul_one]
    rfl
  ·
    intro τ y
    have e : liftAll (fHom K G M D amb χ Δ w hw hww) (θ K G M Δ ⟨w, hw⟩) (θ K G M Δ ⟨wbar, hwbar⟩) hθw hθb hθwb hf0 hf1
        (ιS D τ) = fHom K G M D amb χ Δ w hw hww τ := by
      rw [liftAll_apply, ιS_apply]; simp
    rw [e, fHom_apply, mul_smul]
    by_cases hχ : χ τ = 1
    · rw [if_pos hχ, hχ, lift_one, one_smul, one_smul]; rfl
    · rw [if_neg hχ]
      have : lift (θ K G M Δ ⟨w, hw⟩) (χ τ) = θ K G M Δ ⟨w, hw⟩ := if_neg hχ
      rw [this]; rfl
  ·
    intro y
    have e : liftAll (fHom K G M D amb χ Δ w hw hww) (θ K G M Δ ⟨w, hw⟩) (θ K G M Δ ⟨wbar, hwbar⟩) hθw hθb hθwb hf0 hf1
        (σ₀ D) = θ K G M Δ ⟨w, hw⟩ := by
      rw [liftAll_apply]; simp [σ₀, fHom_apply]
    rw [e]; rfl
  ·
    intro y
    have e : liftAll (fHom K G M D amb χ Δ w hw hww) (θ K G M Δ ⟨w, hw⟩) (θ K G M Δ ⟨wbar, hwbar⟩) hθw hθb hθwb hf0 hf1
        (σ₁ D) = θ K G M Δ ⟨wbar, hwbar⟩ := by
      rw [liftAll_apply]; simp [σ₁, fHom_apply]
    rw [e]; rfl

end S_CerednikDrinfeld_Mumford_exists_symmetryGroup_semilinearAut_invariantFieldOf
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_exists_symmetryGroup_semilinearAut_invariantFieldOf (solution)
