-- Prove2me | solution 1 for FutileDynamics.StaticOpt.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:59:25.822172+00:00
-- url     : https://prove2.me/submissions/9fb67456-9792-4a57-84be-630ae8e0a1be

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model
open MeasureTheory FutileDynamics.StaticOpt

/-- Past noise of rounds `1, …, k`: shocks, agent uniforms, principal uniforms. -/
abbrev FPast (Θ : Type) (k : ℕ) := (Fin k → Θ) × (Fin k → unitInterval) × (Fin k → unitInterval)

open Classical in
/-- The play of the first `n ≤ k` rounds, driven by a given Round 0 report `m₀` and past noise `π`. -/
noncomputable def futileAux_histM {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (m0 : A.M0) (k : ℕ)
    (π : FPast Θ k) : (n : ℕ) → n ≤ k → ((j : Fin n) → A.M j) × (Fin n → Ω)
  | 0, _ => (fun j => j.elim0, fun j => j.elim0)
  | n + 1, hn =>
    let p := futileAux_histM G A σ F m0 k π n (Nat.le_of_succ_le hn)
    let kk : Fin k := ⟨n, hn⟩
    let m : A.M n := σ.s n F (π.1 kk) (fun j => π.1 ⟨j, by omega⟩) m0 p.1 p.2 (π.2.1 kk)
    let ω : Ω := if m0 = A.quit then G.noInt else A.rule n m m0 p.1 p.2 (π.2.2 kk)
    (Fin.snoc (α := fun i : Fin (n + 1) => A.M i) p.1 m, Fin.snoc p.2 ω)

/-- Restriction of the noise to the first `k` rounds. -/
def futileAux_restrict {Θ : Type} {T : ℕ} (k : ℕ) (hk : k ≤ T) (ξ : Noise Θ T) : FPast Θ k :=
  (fun j => ξ.1 ⟨j, by omega⟩, fun j => ξ.2.2.1 ⟨j, by omega⟩, fun j => ξ.2.2.2 ⟨j, by omega⟩)

lemma futileAux_hist_eq_histM {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (k : ℕ)
    (hk : k ≤ T) : ∀ n (hn : n ≤ k), hist G A σ F T ξ n (hn.trans hk) =
      futileAux_histM G A σ F (σ.s0 F ξ.2.1) k (futileAux_restrict k hk ξ) n hn := by
  intro n
  induction n with
  | zero => intro hn; simp only [hist, futileAux_histM]
  | succ n ih =>
    intro hn
    rw [hist, futileAux_histM, ← ih (Nat.le_of_succ_le hn)]
    rfl

lemma futileAux_hist_prefix {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (n : ℕ)
    (j : ℕ) (hj : j < n) : ∀ m (hnm : n ≤ m) (hm : m ≤ T),
      (hist G A σ F T ξ m hm).2 ⟨j, by omega⟩ = (hist G A σ F T ξ n (hnm.trans hm)).2 ⟨j, hj⟩ := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => intro hm; rfl
  | succ m hnm ih =>
    intro hm
    rw [← ih (Nat.le_of_succ_le hm), hist]
    exact Fin.snoc_castSucc (α := fun _ => Ω) (i := ⟨j, by omega⟩) _ _

open Classical in
/-- The outcome of round `k + 1` as a function of the Round 0 report, the current shock, the past noise
and the current uniforms. -/
noncomputable def futileAux_roundOut {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (k : ℕ) (m0 : A.M0) (θc : Θ)
    (π : FPast Θ k) (yk zk : unitInterval) : Ω :=
  if m0 = A.quit then G.noInt else
    A.rule k (σ.s k F θc π.1 m0 (futileAux_histM G A σ F m0 k π k le_rfl).1
      (futileAux_histM G A σ F m0 k π k le_rfl).2 yk) m0 (futileAux_histM G A σ F m0 k π k le_rfl).1
      (futileAux_histM G A σ F m0 k π k le_rfl).2 zk

lemma futileAux_outcome_eq {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (k : Fin T) :
    outcome G A σ F T ξ k = futileAux_roundOut G A σ F k (σ.s0 F ξ.2.1) (ξ.1 k)
      (futileAux_restrict k (le_of_lt k.2) ξ) (ξ.2.2.1 k) (ξ.2.2.2 k) := by
  unfold outcome
  have h1 := futileAux_hist_prefix G A σ F T ξ (k + 1) k (by omega) T (by omega) le_rfl
  rw [show (⟨(k : ℕ), _⟩ : Fin T) = k from rfl] at h1
  rw [h1, hist]
  have h2 := futileAux_hist_eq_histM G A σ F T ξ k (le_of_lt k.2) k le_rfl
  simp only [Fin.snoc_last]
  rw [show (⟨(k : ℕ), by omega⟩ : Fin (k + 1)) = Fin.last k from rfl]
  simp only [Fin.snoc_last]
  unfold futileAux_roundOut
  rw [← h2]
  rfl

open Classical in
/-- Joint measurability of the driven play in `(F, m₀, π)`. -/
lemma futileAux_histM_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (hσ : σ.Feasible) (k : ℕ) :
    ∀ n (hn : n ≤ k), Measurable (fun q : Measure Θ × A.M0 × FPast Θ k =>
      futileAux_histM G A σ q.1 q.2.1 k q.2.2 n hn) := by
  intro n
  induction n with
  | zero =>
    intro hn
    simp only [futileAux_histM]
    exact measurable_const
  | succ n ih =>
    intro hn
    have hp := ih (Nat.le_of_succ_le hn)
    set kk : Fin k := ⟨n, hn⟩
    have hm : Measurable (fun q : Measure Θ × A.M0 × FPast Θ k => σ.s n q.1 (q.2.2.1 kk)
        (fun j => q.2.2.1 ⟨j, by omega⟩) q.2.1
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2 (q.2.2.2.1 kk)) := by
      refine (hσ.2 n).comp (f := fun q : Measure Θ × A.M0 × FPast Θ k => (q.1, q.2.2.1 kk,
        (fun j : Fin n => q.2.2.1 ⟨j, by omega⟩), q.2.1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2, q.2.2.2.1 kk)) ?_
      refine measurable_fst.prodMk (((measurable_pi_apply kk).comp measurable_snd.snd.fst).prodMk
        ((measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd.snd.fst).prodMk
        (measurable_snd.fst.prodMk (hp.fst.prodMk (hp.snd.prodMk
        ((measurable_pi_apply kk).comp measurable_snd.snd.snd.fst))))))
    have hω : Measurable (fun q : Measure Θ × A.M0 × FPast Θ k =>
        if q.2.1 = A.quit then G.noInt else A.rule n (σ.s n q.1 (q.2.2.1 kk)
          (fun j => q.2.2.1 ⟨j, by omega⟩) q.2.1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2 (q.2.2.2.1 kk)) q.2.1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2 (q.2.2.2.2 kk)) := by
      refine Measurable.ite (measurable_snd.fst (measurableSet_singleton A.quit)) measurable_const ?_
      exact (A.rule_meas n).comp (hm.prodMk (measurable_snd.fst.prodMk (hp.fst.prodMk (hp.snd.prodMk
        ((measurable_pi_apply kk).comp measurable_snd.snd.snd.snd)))))
    simp only [futileAux_histM]
    refine Measurable.prodMk ?_ ?_
    · refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact hm
      · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply _).comp hp.fst
    · refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact hω
      · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply _).comp hp.snd

/-- Arguments of `futileAux_roundOut`. -/
abbrev RArg (Θ M0 : Type) [MeasurableSpace Θ] (k : ℕ) := Measure Θ × M0 × Θ × FPast Θ k × unitInterval × unitInterval

open Classical in
lemma futileAux_roundOut_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (hσ : σ.Feasible) (k : ℕ) :
    Measurable (fun q : RArg Θ A.M0 k =>
      futileAux_roundOut G A σ q.1 k q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  have hf : Measurable (fun q : RArg Θ A.M0 k => (q.1, q.2.1, q.2.2.2.1)) := by fun_prop
  have hp := (futileAux_histM_meas G A σ hσ k k le_rfl).comp hf
  have hm : Measurable (fun q : RArg Θ A.M0 k =>
      σ.s k q.1 q.2.2.1 q.2.2.2.1.1 q.2.1 (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).1
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).2 q.2.2.2.2.1) := by
    have h2 : Measurable (fun q : RArg Θ A.M0 k => (q.1, q.2.2.1, q.2.2.2.1.1, q.2.1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).2, q.2.2.2.2.1)) := by
      refine measurable_fst.prodMk (measurable_snd.snd.fst.prodMk
        (measurable_snd.snd.snd.fst.fst.prodMk (measurable_snd.fst.prodMk (hp.fst.prodMk
        (hp.snd.prodMk measurable_snd.snd.snd.snd.fst)))))
    exact (hσ.2 k).comp h2
  unfold futileAux_roundOut
  refine Measurable.ite (measurable_snd.fst (measurableSet_singleton A.quit)) measurable_const ?_
  exact (A.rule_meas k).comp (hm.prodMk (measurable_snd.fst.prodMk (hp.fst.prodMk (hp.snd.prodMk
    measurable_snd.snd.snd.snd.snd))))

section Rearrange
variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

lemma futileAux_mp_assoc (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb]
    [SFinite μc] : MeasurePreserving (fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2)))
      ((μa.prod μb).prod μc) (μa.prod (μb.prod μc)) :=
  measurePreserving_prodAssoc μa μb μc

lemma futileAux_mp_assoc_symm (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa]
    [SFinite μb] [SFinite μc] : MeasurePreserving (fun p : α × (β × γ) => ((p.1, p.2.1), p.2.2))
      (μa.prod (μb.prod μc)) ((μa.prod μb).prod μc) :=
  (measurePreserving_prodAssoc μa μb μc).symm

lemma futileAux_mp_leftComm (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa]
    [SFinite μb] [SFinite μc] : MeasurePreserving (fun p : α × (β × γ) => (p.2.1, (p.1, p.2.2)))
      (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have h := (futileAux_mp_assoc μb μa μc).comp (((Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod
    (MeasurePreserving.id μc)).comp (futileAux_mp_assoc_symm μa μb μc))
  exact h

lemma futileAux_mp_mid4 (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h := (futileAux_mp_assoc_symm μa μc (μb.prod μd)).comp
    (((MeasurePreserving.id μa).prod (futileAux_mp_leftComm μb μc μd)).comp
      (futileAux_mp_assoc μa μb (μc.prod μd)))
  exact h

end Rearrange

/-- Splitting off coordinate `k` and the coordinates before it. -/
lemma futileAux_splitAt {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (T : ℕ)
    (k : Fin T) : MeasurePreserving (fun x : Fin T → α => (x k, fun j : Fin k => x ⟨j, by omega⟩))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin k => μ)) := by
  classical
  let p : Fin T → Prop := fun i => i.val < k.val
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin T => μ) p
  let f : Fin k ≃ {i : Fin T // p i} :=
    { toFun := fun j => ⟨⟨j, by omega⟩, j.2⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun j => rfl
      right_inv := fun i => rfl }
  have h2 := (measurePreserving_piCongrLeft (fun _ : {i : Fin T // p i} => μ) f).symm
  have h3 := measurePreserving_eval (fun _ : {i : Fin T // ¬ p i} => μ) ⟨k, lt_irrefl _⟩
  have h5 := (Measure.measurePreserving_swap).comp ((h2.prod h3).comp h1)
  convert h5 using 1
  funext x
  refine Prod.ext rfl ?_
  funext j
  simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.piEquivPiSubtypeProd, f]

/-- The law of the past noise of `k` rounds. -/
noncomputable def futileAux_W {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) (k : ℕ) : Measure (FPast Θ k) :=
  (Measure.pi fun _ : Fin k => F).prod ((Measure.pi fun _ : Fin k => (volume : Measure unitInterval)).prod
    (Measure.pi fun _ : Fin k => (volume : Measure unitInterval)))

/-- The canonical law of `(θ_k, y₀, past noise, y_k, z_k)`. -/
noncomputable def futileAux_Q {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) (k : ℕ) :
    Measure (Θ × unitInterval × FPast Θ k × unitInterval × unitInterval) :=
  F.prod ((volume : Measure unitInterval).prod ((futileAux_W F k).prod
    ((volume : Measure unitInterval).prod (volume : Measure unitInterval))))

instance futileAux_W_prob {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F]
    (k : ℕ) : IsProbabilityMeasure (futileAux_W F k) := by unfold futileAux_W; infer_instance

lemma futileAux_mp_T {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ)
    (k : Fin T) : MeasurePreserving (fun ξ : Noise Θ T => (ξ.1 k, (ξ.2.1,
      (futileAux_restrict k (le_of_lt k.2) ξ, (ξ.2.2.1 k, ξ.2.2.2 k))))) (noiseLaw F T) (futileAux_Q F k) := by
  set Lv := (volume : Measure unitInterval)
  set PF := Measure.pi fun _ : Fin k => F
  set PL := Measure.pi fun _ : Fin k => Lv
  have s0 := (futileAux_splitAt F T k).prod ((MeasurePreserving.id Lv).prod
    ((futileAux_splitAt Lv T k).prod (futileAux_splitAt Lv T k)))
  have r1 := futileAux_mp_assoc F PF (Lv.prod ((Lv.prod PL).prod (Lv.prod PL)))
  have r2 := (MeasurePreserving.id F).prod (futileAux_mp_leftComm PF Lv ((Lv.prod PL).prod (Lv.prod PL)))
  have r3 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    ((MeasurePreserving.id PF).prod (futileAux_mp_mid4 Lv PL Lv PL)))
  have r4 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (futileAux_mp_leftComm PF (Lv.prod Lv) (PL.prod PL)))
  have r5 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (Measure.measurePreserving_swap (μ := Lv.prod Lv) (ν := PF.prod (PL.prod PL))))
  have h := r5.comp (r4.comp (r3.comp (r2.comp (r1.comp s0))))
  exact h

lemma futileAux_mp_1 {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F] (k : ℕ)
    (sp : unitInterval → FPast Θ k × unitInterval)
    (hs : MeasurePreserving sp (volume : Measure unitInterval) ((futileAux_W F k).prod volume)) :
    MeasurePreserving (fun ξ : Noise Θ 1 => (ξ.1 0, (ξ.2.1, ((sp (ξ.2.2.1 0)).1,
      ((sp (ξ.2.2.1 0)).2, ξ.2.2.2 0))))) (noiseLaw F 1) (futileAux_Q F k) := by
  set Lv := (volume : Measure unitInterval)
  have u0 := (measurePreserving_funUnique F (Fin 1)).prod ((MeasurePreserving.id Lv).prod
    ((measurePreserving_funUnique Lv (Fin 1)).prod (measurePreserving_funUnique Lv (Fin 1))))
  have u1 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (hs.prod (MeasurePreserving.id Lv)))
  have u2 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (futileAux_mp_assoc (futileAux_W F k) Lv Lv))
  have h := u2.comp (u1.comp u0)
  exact h

/-- A jointly measurable sampler: `samp F` pushes the uniform law to `F` for every probability `F`. -/
lemma futileAux_sampler (Θ : Type) [MeasurableSpace Θ] [StandardBorelSpace Θ] [Nonempty Θ] :
    ∃ samp : Measure Θ → unitInterval → Θ, Measurable (Function.uncurry samp) ∧
      ∀ F : Measure Θ, IsProbabilityMeasure F → (volume : Measure unitInterval).map (samp F) = F := by
  classical
  let θ0 : Θ := Classical.arbitrary Θ
  have hS : MeasurableSet {F : Measure Θ | F Set.univ = 1} :=
    Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  let κ : ProbabilityTheory.Kernel (Measure Θ) Θ :=
    ⟨fun F => if F Set.univ = 1 then F else Measure.dirac θ0,
      Measurable.ite hS measurable_id measurable_const⟩
  have hκ : ProbabilityTheory.IsMarkovKernel κ := by
    refine ⟨fun F => ?_⟩
    show IsProbabilityMeasure (if F Set.univ = 1 then F else Measure.dirac θ0)
    split_ifs with h
    · exact ⟨h⟩
    · infer_instance
  obtain ⟨f, hf, hfκ⟩ := κ.exists_measurable_map_eq_unitInterval
  refine ⟨f, hf, fun F hF => ?_⟩
  rw [hfκ F]
  show (if F Set.univ = 1 then F else Measure.dirac θ0) = F
  rw [if_pos hF.measure_univ]

/-- A jointly measurable splitter turning one uniform into an independent past noise of `k` rounds
(with shocks drawn from `F`) and one further uniform. -/
lemma futileAux_splitter (Θ : Type) [MeasurableSpace Θ] [StandardBorelSpace Θ] [Nonempty Θ] (k : ℕ) :
    ∃ sp : Measure Θ → unitInterval → FPast Θ k × unitInterval, Measurable (Function.uncurry sp) ∧
      ∀ F : Measure Θ, IsProbabilityMeasure F →
        MeasurePreserving (sp F) (volume : Measure unitInterval) ((futileAux_W F k).prod volume) := by
  obtain ⟨samp, hsamp, hsampF⟩ := futileAux_sampler Θ
  haveI : StandardBorelSpace (Fin k → unitInterval) := inferInstance
  haveI : StandardBorelSpace ((Fin k → unitInterval) × (Fin k → unitInterval)) := inferInstance
  haveI : StandardBorelSpace ((Fin k → unitInterval) × (Fin k → unitInterval) × (Fin k → unitInterval)) :=
    inferInstance
  haveI : StandardBorelSpace (((Fin k → unitInterval) × (Fin k → unitInterval) × (Fin k → unitInterval)) ×
    unitInterval) := inferInstance
  obtain ⟨split, hsm, hsmap⟩ := Measure.exists_measurable_map_eq
    (((Measure.pi fun _ : Fin k => (volume : Measure unitInterval)).prod
      ((Measure.pi fun _ : Fin k => (volume : Measure unitInterval)).prod
        (Measure.pi fun _ : Fin k => (volume : Measure unitInterval)))).prod (volume : Measure unitInterval))
  refine ⟨fun F y => ((fun j => samp F ((split y).1.1 j), (split y).1.2), (split y).2), ?_, fun F hF => ?_⟩
  · have hs2 : Measurable (fun p : Measure Θ × unitInterval => split p.2) := hsm.comp measurable_snd
    refine Measurable.prodMk (Measurable.prodMk ?_ hs2.fst.snd) hs2.snd
    refine measurable_pi_lambda _ fun j => ?_
    exact hsamp.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp hs2.fst.fst))
  · have hA : MeasurePreserving (fun u : Fin k → unitInterval => fun j => samp F (u j))
        (Measure.pi fun _ : Fin k => (volume : Measure unitInterval)) (Measure.pi fun _ : Fin k => F) := by
      have hmeas : Measurable (fun u : Fin k → unitInterval => fun j => samp F (u j)) :=
        measurable_pi_lambda _ fun j => (hsamp.comp (measurable_const.prodMk measurable_id)).comp
          (measurable_pi_apply j)
      refine ⟨hmeas, ?_⟩
      have := Measure.pi_map_pi (μ := fun _ : Fin k => (volume : Measure unitInterval))
        (f := fun _ => samp F)
        (fun _ => (hsamp.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      rw [this]
      congr 1
      funext i
      exact hsampF F hF
    have hS : MeasurePreserving split (volume : Measure unitInterval)
        (((Measure.pi fun _ : Fin k => (volume : Measure unitInterval)).prod
          ((Measure.pi fun _ : Fin k => (volume : Measure unitInterval)).prod
            (Measure.pi fun _ : Fin k => (volume : Measure unitInterval)))).prod
              (volume : Measure unitInterval)) := ⟨hsm, hsmap⟩
    have h := ((hA.prod (MeasurePreserving.id _)).prod (MeasurePreserving.id _)).comp hS
    exact h

theorem solution {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) (d : DirectRule G) (F' : Measure Θ)
    (hF' : IsProbabilityMeasure F')
    (σ' : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M) (hσ' : σ'.Feasible) (k : Fin T) :
    ∃ σ'' : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M, σ''.Feasible ∧
      agentUtility G (repeatDirect G d) σ'' F' 1 = roundAgentUtility G (repeatDirect G d) σ' F' T k ∧
      principalUtility G (repeatDirect G d) σ'' F' 1 =
        roundPrincipalUtility G (repeatDirect G d) σ' F' T k := by
  obtain ⟨sp, hspm, hspF⟩ := futileAux_splitter Θ k
  let σ'' : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M :=
    { s0 := σ'.s0
      s := fun n F θ _ m0 _ _ y =>
        (σ'.s k F θ (sp F y).1.1 m0 (futileAux_histM G (repeatDirect G d) σ' F m0 k (sp F y).1 k le_rfl).1
          (futileAux_histM G (repeatDirect G d) σ' F m0 k (sp F y).1 k le_rfl).2 (sp F y).2 : Θ × Bool) }
  have hfeas : σ''.Feasible := by
    refine ⟨hσ'.1, fun n => ?_⟩
    have hsp' : Measurable (fun p : Measure Θ × Θ × (Fin n → Θ) × (repeatDirect G d).M0 × ((j : Fin n) → (repeatDirect G d).M j) ×
        (Fin n → Ω) × unitInterval => sp p.1 p.2.2.2.2.2.2) :=
      hspm.comp (measurable_fst.prodMk measurable_snd.snd.snd.snd.snd.snd)
    have hH := (futileAux_histM_meas G (repeatDirect G d) σ' hσ' k k le_rfl).comp
      (measurable_fst.prodMk (measurable_snd.snd.snd.fst.prodMk hsp'.fst))
    exact (hσ'.2 k).comp (measurable_fst.prodMk (measurable_snd.fst.prodMk (hsp'.fst.fst.prodMk
      (measurable_snd.snd.snd.fst.prodMk (hH.fst.prodMk (hH.snd.prodMk hsp'.snd))))))
  have hout1 : ∀ ξ : Noise Θ 1, outcome G (repeatDirect G d) σ'' F' 1 ξ 0 = futileAux_roundOut G (repeatDirect G d) σ' F' k
      (σ'.s0 F' ξ.2.1) (ξ.1 0) (sp F' (ξ.2.2.1 0)).1 (sp F' (ξ.2.2.1 0)).2 (ξ.2.2.2 0) := by
    intro ξ
    unfold outcome
    rw [hist]
    rfl
  have key : ∀ w : Θ → Ω → ℝ, Measurable (Function.uncurry w) → ∀ B : ℝ, (∀ θ ω, |w θ ω| ≤ B) →
      ∫ ξ, w (ξ.1 0) (outcome G (repeatDirect G d) σ'' F' 1 ξ 0) ∂(noiseLaw F' 1) =
        ∫ ξ, w (ξ.1 k) (outcome G (repeatDirect G d) σ' F' T ξ k) ∂(noiseLaw F' T) := by
    intro w hw B hB
    let J : Θ × unitInterval × FPast Θ k × unitInterval × unitInterval → ℝ := fun c =>
      w c.1 (futileAux_roundOut G (repeatDirect G d) σ' F' k (σ'.s0 F' c.2.1) c.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)
    have hJ : Measurable J := by
      have h0 : Measurable (fun c : Θ × unitInterval × FPast Θ k × unitInterval × unitInterval =>
          ((F', σ'.s0 F' c.2.1, c.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2) : RArg Θ (repeatDirect G d).M0 k)) :=
        measurable_const.prodMk ((hσ'.1.comp (measurable_const.prodMk measurable_snd.fst)).prodMk
          (measurable_fst.prodMk (measurable_snd.snd.fst.prodMk (measurable_snd.snd.snd.fst.prodMk
          measurable_snd.snd.snd.snd))))
      exact hw.comp (measurable_fst.prodMk ((futileAux_roundOut_meas G (repeatDirect G d) σ' hσ' k).comp h0))
    have hT' := futileAux_mp_T F' T k
    have h1' := futileAux_mp_1 F' k (sp F') (hspF F' hF')
    have eT : ∫ ξ, w (ξ.1 k) (outcome G (repeatDirect G d) σ' F' T ξ k) ∂(noiseLaw F' T) = ∫ c, J c ∂(futileAux_Q F' k) := by
      rw [← hT'.map_eq, integral_map hT'.measurable.aemeasurable
        (hT'.map_eq ▸ hJ.aestronglyMeasurable)]
      congr 1
      funext ξ
      try rw [futileAux_outcome_eq]
    have e1 : ∫ ξ, w (ξ.1 0) (outcome G (repeatDirect G d) σ'' F' 1 ξ 0) ∂(noiseLaw F' 1) = ∫ c, J c ∂(futileAux_Q F' k) := by
      rw [← h1'.map_eq, integral_map h1'.measurable.aemeasurable
        (h1'.map_eq ▸ hJ.aestronglyMeasurable)]
      congr 1
    rw [eT, e1]
  obtain ⟨B, hB⟩ := G.bdd
  refine ⟨σ'', hfeas, ?_, ?_⟩
  · unfold agentUtility roundAgentUtility
    simp only [Fin.sum_univ_one]
    exact key G.v G.v_meas B (fun θ ω => (hB θ ω).2)
  · unfold principalUtility roundPrincipalUtility
    simp only [Fin.sum_univ_one]
    exact key G.u G.u_meas B (fun θ ω => (hB θ ω).1)
